// Lean compiler output
// Module: Std.Data.ExtHashMap.Basic
// Imports: Std.Data.ExtDHashMap.Basic
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0,
};
use crate::r#gen::Init::Data::List::Control::l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go,
    l_Std_DHashMap_Internal_AssocList_contains___redArg,
    l_Std_DHashMap_Internal_AssocList_get_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_replace___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_erase___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_expand___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_inter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_map___redArg,
};
use crate::r#gen::Std::Data::DHashMap::RawDef::l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2;
use crate::r#gen::Std::Data::ExtDHashMap::Basic::{
    initialize_Std_Data_ExtDHashMap_Basic, runtime_initialize_Std_Data_ExtDHashMap_Basic,
};
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{lean_usize_of_nat, lean_usize_sub};
use crate::ffi::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_div, lean_nat_mul,
};
static mut l_Std_ExtHashMap_instEmptyCollection___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtHashMap_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtHashMap_instEmptyCollection___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtHashMap_instEmptyCollection___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtHashMap_ofList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__10_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_ofList___redArg___closed__11_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashMap_ofList___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_union___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashMap_union___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_union___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_unitOfArray___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtHashMap_ofList___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_ExtHashMap_unitOfArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_unitOfArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashMap_unitOfArray___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtHashMap_unitOfArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_ExtHashMap_unitOfArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashMap_unitOfArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_ExtHashMap_emptyWithCapacity___redArg(
    mut v_capacity_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1303_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1304_ = lean_nat_mul(v_capacity_1301_, v___x_1303_);
    v___x_1305_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1306_ = lean_nat_div(v___x_1304_, v___x_1305_);
    crate::leanh::lean_dec(v___x_1304_);
    v___x_1307_ = l_Nat_nextPowerOfTwo(v___x_1306_);
    crate::leanh::lean_dec(v___x_1306_);
    v___x_1308_ = crate::leanh::lean_box(0);
    v___x_1309_ = lean_mk_array(v___x_1307_, v___x_1308_);
    v___x_1310_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1310_, 0, v___x_1302_);
    crate::leanh::lean_ctor_set(v___x_1310_, 1, v___x_1309_);
    return v___x_1310_;
}
pub unsafe fn l_Std_ExtHashMap_emptyWithCapacity___redArg___boxed(
    mut v_capacity_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1312_ = l_Std_ExtHashMap_emptyWithCapacity___redArg(v_capacity_1311_);
    crate::leanh::lean_dec(v_capacity_1311_);
    return v_res_1312_;
}
pub unsafe fn l_Std_ExtHashMap_emptyWithCapacity(
    mut v_00_u03b1_1313_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1314_: *mut crate::leanh::LeanObject,
    mut v_inst_1315_: *mut crate::leanh::LeanObject,
    mut v_inst_1316_: *mut crate::leanh::LeanObject,
    mut v_capacity_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1318_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1319_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1320_ = lean_nat_mul(v_capacity_1317_, v___x_1319_);
    v___x_1321_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1322_ = lean_nat_div(v___x_1320_, v___x_1321_);
    crate::leanh::lean_dec(v___x_1320_);
    v___x_1323_ = l_Nat_nextPowerOfTwo(v___x_1322_);
    crate::leanh::lean_dec(v___x_1322_);
    v___x_1324_ = crate::leanh::lean_box(0);
    v___x_1325_ = lean_mk_array(v___x_1323_, v___x_1324_);
    v___x_1326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1326_, 0, v___x_1318_);
    crate::leanh::lean_ctor_set(v___x_1326_, 1, v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Std_ExtHashMap_emptyWithCapacity___boxed(
    mut v_00_u03b1_1327_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1328_: *mut crate::leanh::LeanObject,
    mut v_inst_1329_: *mut crate::leanh::LeanObject,
    mut v_inst_1330_: *mut crate::leanh::LeanObject,
    mut v_capacity_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1332_ = l_Std_ExtHashMap_emptyWithCapacity(
        v_00_u03b1_1327_,
        v_00_u03b2_1328_,
        v_inst_1329_,
        v_inst_1330_,
        v_capacity_1331_,
    );
    crate::leanh::lean_dec(v_capacity_1331_);
    crate::leanh::lean_dec_ref(v_inst_1330_);
    crate::leanh::lean_dec_ref(v_inst_1329_);
    return v_res_1332_;
}
pub unsafe fn _init_l_Std_ExtHashMap_instEmptyCollection___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = crate::leanh::lean_box(0);
    v___x_1334_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1335_ = lean_mk_array(v___x_1334_, v___x_1333_);
    return v___x_1335_;
}
pub unsafe fn _init_l_Std_ExtHashMap_instEmptyCollection___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1336_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__0_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__0,
    );
    v___x_1337_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1338_, 0, v___x_1337_);
    crate::leanh::lean_ctor_set(v___x_1338_, 1, v___x_1336_);
    return v___x_1338_;
}
pub unsafe fn l_Std_ExtHashMap_instEmptyCollection(
    mut v_00_u03b1_1339_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1340_: *mut crate::leanh::LeanObject,
    mut v_inst_1341_: *mut crate::leanh::LeanObject,
    mut v_inst_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    return v___x_1343_;
}
pub unsafe fn l_Std_ExtHashMap_instEmptyCollection___boxed(
    mut v_00_u03b1_1344_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1345_: *mut crate::leanh::LeanObject,
    mut v_inst_1346_: *mut crate::leanh::LeanObject,
    mut v_inst_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1348_ = l_Std_ExtHashMap_instEmptyCollection(
        v_00_u03b1_1344_,
        v_00_u03b2_1345_,
        v_inst_1346_,
        v_inst_1347_,
    );
    crate::leanh::lean_dec_ref(v_inst_1347_);
    crate::leanh::lean_dec_ref(v_inst_1346_);
    return v_res_1348_;
}
pub unsafe fn l_Std_ExtHashMap_instInhabited(
    mut v_00_u03b1_1349_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1350_: *mut crate::leanh::LeanObject,
    mut v_inst_1351_: *mut crate::leanh::LeanObject,
    mut v_inst_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    return v___x_1353_;
}
pub unsafe fn l_Std_ExtHashMap_instInhabited___boxed(
    mut v_00_u03b1_1354_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1355_: *mut crate::leanh::LeanObject,
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Std_ExtHashMap_instInhabited(
        v_00_u03b1_1354_,
        v_00_u03b2_1355_,
        v_inst_1356_,
        v_inst_1357_,
    );
    crate::leanh::lean_dec_ref(v_inst_1357_);
    crate::leanh::lean_dec_ref(v_inst_1356_);
    return v_res_1358_;
}
pub unsafe fn l_Std_ExtHashMap_insert___redArg(
    mut v_x_1359_: *mut crate::leanh::LeanObject,
    mut v_x_1360_: *mut crate::leanh::LeanObject,
    mut v_m_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
    mut v_b_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1364_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1359_, v_x_1360_, v_m_1361_, v_a_1362_, v_b_1363_,
    );
    return v___x_1364_;
}
pub unsafe fn l_Std_ExtHashMap_insert(
    mut v_00_u03b1_1365_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1366_: *mut crate::leanh::LeanObject,
    mut v_x_1367_: *mut crate::leanh::LeanObject,
    mut v_x_1368_: *mut crate::leanh::LeanObject,
    mut v_inst_1369_: *mut crate::leanh::LeanObject,
    mut v_inst_1370_: *mut crate::leanh::LeanObject,
    mut v_m_1371_: *mut crate::leanh::LeanObject,
    mut v_a_1372_: *mut crate::leanh::LeanObject,
    mut v_b_1373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1367_, v_x_1368_, v_m_1371_, v_a_1372_, v_b_1373_,
    );
    return v___x_1374_;
}
pub unsafe fn l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1375_: *mut crate::leanh::LeanObject,
    mut v_x_1376_: *mut crate::leanh::LeanObject,
    mut v_x_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1378_ = crate::leanh::lean_ctor_get(v_x_1377_, 0);
    crate::leanh::lean_inc(v_fst_1378_);
    v_snd_1379_ = crate::leanh::lean_ctor_get(v_x_1377_, 1);
    crate::leanh::lean_inc(v_snd_1379_);
    crate::leanh::lean_dec_ref(v_x_1377_);
    v___x_1380_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    v___x_1381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1375_,
        v_x_1376_,
        v___x_1380_,
        v_fst_1378_,
        v_snd_1379_,
    );
    return v___x_1381_;
}
pub unsafe fn l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_1382_: *mut crate::leanh::LeanObject,
    mut v_x_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1384_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1384_, 0, v_x_1382_);
    crate::leanh::lean_closure_set(v___f_1384_, 1, v_x_1383_);
    return v___f_1384_;
}
pub unsafe fn l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1385_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1386_: *mut crate::leanh::LeanObject,
    mut v_x_1387_: *mut crate::leanh::LeanObject,
    mut v_x_1388_: *mut crate::leanh::LeanObject,
    mut v_inst_1389_: *mut crate::leanh::LeanObject,
    mut v_inst_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1391_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1391_, 0, v_x_1387_);
    crate::leanh::lean_closure_set(v___f_1391_, 1, v_x_1388_);
    return v___f_1391_;
}
pub unsafe fn l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1392_: *mut crate::leanh::LeanObject,
    mut v_x_1393_: *mut crate::leanh::LeanObject,
    mut v_x_1394_: *mut crate::leanh::LeanObject,
    mut v_x_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1396_ = crate::leanh::lean_ctor_get(v_x_1394_, 0);
    crate::leanh::lean_inc(v_fst_1396_);
    v_snd_1397_ = crate::leanh::lean_ctor_get(v_x_1394_, 1);
    crate::leanh::lean_inc(v_snd_1397_);
    crate::leanh::lean_dec_ref(v_x_1394_);
    v___x_1398_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1392_,
        v_x_1393_,
        v_x_1395_,
        v_fst_1396_,
        v_snd_1397_,
    );
    return v___x_1398_;
}
pub unsafe fn l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_1399_: *mut crate::leanh::LeanObject,
    mut v_x_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1401_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1401_, 0, v_x_1399_);
    crate::leanh::lean_closure_set(v___f_1401_, 1, v_x_1400_);
    return v___f_1401_;
}
pub unsafe fn l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1402_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1403_: *mut crate::leanh::LeanObject,
    mut v_x_1404_: *mut crate::leanh::LeanObject,
    mut v_x_1405_: *mut crate::leanh::LeanObject,
    mut v_inst_1406_: *mut crate::leanh::LeanObject,
    mut v_inst_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1408_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1408_, 0, v_x_1404_);
    crate::leanh::lean_closure_set(v___f_1408_, 1, v_x_1405_);
    return v___f_1408_;
}
pub unsafe fn l_Std_ExtHashMap_insertIfNew___redArg(
    mut v_x_1409_: *mut crate::leanh::LeanObject,
    mut v_x_1410_: *mut crate::leanh::LeanObject,
    mut v_m_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_b_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1409_, v_x_1410_, v_m_1411_, v_a_1412_, v_b_1413_,
    );
    return v___x_1414_;
}
pub unsafe fn l_Std_ExtHashMap_insertIfNew(
    mut v_00_u03b1_1415_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1416_: *mut crate::leanh::LeanObject,
    mut v_x_1417_: *mut crate::leanh::LeanObject,
    mut v_x_1418_: *mut crate::leanh::LeanObject,
    mut v_inst_1419_: *mut crate::leanh::LeanObject,
    mut v_inst_1420_: *mut crate::leanh::LeanObject,
    mut v_m_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_b_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1417_, v_x_1418_, v_m_1421_, v_a_1422_, v_b_1423_,
    );
    return v___x_1424_;
}
pub unsafe fn l_Std_ExtHashMap_containsThenInsert___redArg(
    mut v_x_1425_: *mut crate::leanh::LeanObject,
    mut v_x_1426_: *mut crate::leanh::LeanObject,
    mut v_m_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
    mut v_b_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1434_: u8 = 0;
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u64 = 0;
    let mut v___x_1438_: u64 = 0;
    let mut v___x_1439_: u64 = 0;
    let mut v___x_1440_: u64 = 0;
    let mut v_fold_1441_: u64 = 0;
    let mut v___x_1442_: u64 = 0;
    let mut v___x_1443_: u64 = 0;
    let mut v___x_1444_: u64 = 0;
    let mut v___x_1445_: usize = 0;
    let mut v___x_1446_: usize = 0;
    let mut v___x_1447_: usize = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v_bkt_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v_val_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1430_ = crate::leanh::lean_ctor_get(v_m_1427_, 0);
                v_buckets_1431_ = crate::leanh::lean_ctor_get(v_m_1427_, 1);
                v_isSharedCheck_1482_ = (!crate::leanh::lean_is_exclusive(v_m_1427_)) as u8;
                if v_isSharedCheck_1482_ == 0 {
                    v___x_1433_ = v_m_1427_;
                    v_isShared_1434_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1431_);
                    crate::leanh::lean_inc(v_size_1430_);
                    crate::leanh::lean_dec(v_m_1427_);
                    v___x_1433_ = crate::leanh::lean_box(0);
                    v_isShared_1434_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1435_ = lean_array_get_size(v_buckets_1431_);
                crate::leanh::lean_inc_ref(v_x_1426_);
                crate::leanh::lean_inc_n(v_a_1428_, 2);
                v___x_1436_ = crate::leanh::lean_apply_1(v_x_1426_, v_a_1428_);
                v___x_1437_ = 32u64;
                v___x_1438_ = crate::leanh::lean_unbox_uint64(v___x_1436_);
                v___x_1439_ = lean_uint64_shift_right(v___x_1438_, v___x_1437_);
                v___x_1440_ = crate::leanh::lean_unbox_uint64(v___x_1436_);
                crate::leanh::lean_dec_ref(v___x_1436_);
                v_fold_1441_ = lean_uint64_xor(v___x_1440_, v___x_1439_);
                v___x_1442_ = 16u64;
                v___x_1443_ = lean_uint64_shift_right(v_fold_1441_, v___x_1442_);
                v___x_1444_ = lean_uint64_xor(v_fold_1441_, v___x_1443_);
                v___x_1445_ = lean_uint64_to_usize(v___x_1444_);
                v___x_1446_ = lean_usize_of_nat(v___x_1435_);
                v___x_1447_ = 1usize;
                v___x_1448_ = lean_usize_sub(v___x_1446_, v___x_1447_);
                v___x_1449_ = lean_usize_land(v___x_1445_, v___x_1448_);
                v_bkt_1450_ = lean_array_uget_borrowed(v_buckets_1431_, v___x_1449_);
                crate::leanh::lean_inc(v_bkt_1450_);
                crate::leanh::lean_inc_ref(v_x_1425_);
                v___x_1451_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1425_,
                    v_a_1428_,
                    v_bkt_1450_,
                );
                if v___x_1451_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_1425_);
                    v___x_1452_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1453_ = lean_nat_add(v_size_1430_, v___x_1452_);
                    crate::leanh::lean_dec(v_size_1430_);
                    crate::leanh::lean_inc(v_bkt_1450_);
                    v___x_1454_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1454_, 0, v_a_1428_);
                    crate::leanh::lean_ctor_set(v___x_1454_, 1, v_b_1429_);
                    crate::leanh::lean_ctor_set(v___x_1454_, 2, v_bkt_1450_);
                    v_buckets_x27_1455_ =
                        lean_array_uset(v_buckets_1431_, v___x_1449_, v___x_1454_);
                    v___x_1456_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1457_ = lean_nat_mul(v_size_x27_1453_, v___x_1456_);
                    v___x_1458_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1459_ = lean_nat_div(v___x_1457_, v___x_1458_);
                    crate::leanh::lean_dec(v___x_1457_);
                    v___x_1460_ = lean_array_get_size(v_buckets_x27_1455_);
                    v___x_1461_ = lean_nat_dec_le(v___x_1459_, v___x_1460_);
                    crate::leanh::lean_dec(v___x_1459_);
                    if v___x_1461_ == 0 {
                        v_val_1462_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_1426_,
                            v_buckets_x27_1455_,
                        );
                        if v_isShared_1434_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1433_, 1, v_val_1462_);
                            crate::leanh::lean_ctor_set(v___x_1433_, 0, v_size_x27_1453_);
                            v___x_1464_ = v___x_1433_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1467_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1467_,
                                0,
                                v_size_x27_1453_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_val_1462_);
                            v___x_1464_ = v_reuseFailAlloc_1467_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1426_);
                        if v_isShared_1434_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1433_, 1, v_buckets_x27_1455_);
                            crate::leanh::lean_ctor_set(v___x_1433_, 0, v_size_x27_1453_);
                            v___x_1469_ = v___x_1433_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1472_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1472_,
                                0,
                                v_size_x27_1453_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1472_,
                                1,
                                v_buckets_x27_1455_,
                            );
                            v___x_1469_ = v_reuseFailAlloc_1472_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1450_);
                    crate::leanh::lean_dec_ref(v_x_1426_);
                    v___x_1473_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1474_ =
                        lean_array_uset(v_buckets_1431_, v___x_1449_, v___x_1473_);
                    v___x_1475_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_x_1425_,
                        v_a_1428_,
                        v_b_1429_,
                        v_bkt_1450_,
                    );
                    v___x_1476_ = lean_array_uset(v_buckets_x27_1474_, v___x_1449_, v___x_1475_);
                    if v_isShared_1434_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1433_, 1, v___x_1476_);
                        v___x_1478_ = v___x_1433_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1481_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_size_1430_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1476_);
                        v___x_1478_ = v_reuseFailAlloc_1481_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1465_ = crate::leanh::lean_box((v___x_1451_) as usize);
                v___x_1466_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1466_, 0, v___x_1465_);
                crate::leanh::lean_ctor_set(v___x_1466_, 1, v___x_1464_);
                return v___x_1466_;
            }
            3 => {
                v___x_1470_ = crate::leanh::lean_box((v___x_1451_) as usize);
                v___x_1471_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1471_, 0, v___x_1470_);
                crate::leanh::lean_ctor_set(v___x_1471_, 1, v___x_1469_);
                return v___x_1471_;
            }
            4 => {
                v___x_1479_ = crate::leanh::lean_box((v___x_1451_) as usize);
                v___x_1480_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1480_, 0, v___x_1479_);
                crate::leanh::lean_ctor_set(v___x_1480_, 1, v___x_1478_);
                return v___x_1480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtHashMap_containsThenInsert(
    mut v_00_u03b1_1483_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1484_: *mut crate::leanh::LeanObject,
    mut v_x_1485_: *mut crate::leanh::LeanObject,
    mut v_x_1486_: *mut crate::leanh::LeanObject,
    mut v_inst_1487_: *mut crate::leanh::LeanObject,
    mut v_inst_1488_: *mut crate::leanh::LeanObject,
    mut v_m_1489_: *mut crate::leanh::LeanObject,
    mut v_a_1490_: *mut crate::leanh::LeanObject,
    mut v_b_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u64 = 0;
    let mut v___x_1500_: u64 = 0;
    let mut v___x_1501_: u64 = 0;
    let mut v___x_1502_: u64 = 0;
    let mut v_fold_1503_: u64 = 0;
    let mut v___x_1504_: u64 = 0;
    let mut v___x_1505_: u64 = 0;
    let mut v___x_1506_: u64 = 0;
    let mut v___x_1507_: usize = 0;
    let mut v___x_1508_: usize = 0;
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: usize = 0;
    let mut v___x_1511_: usize = 0;
    let mut v_bkt_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: u8 = 0;
    let mut v_val_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1492_ = crate::leanh::lean_ctor_get(v_m_1489_, 0);
                v_buckets_1493_ = crate::leanh::lean_ctor_get(v_m_1489_, 1);
                v_isSharedCheck_1544_ = (!crate::leanh::lean_is_exclusive(v_m_1489_)) as u8;
                if v_isSharedCheck_1544_ == 0 {
                    v___x_1495_ = v_m_1489_;
                    v_isShared_1496_ = v_isSharedCheck_1544_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1493_);
                    crate::leanh::lean_inc(v_size_1492_);
                    crate::leanh::lean_dec(v_m_1489_);
                    v___x_1495_ = crate::leanh::lean_box(0);
                    v_isShared_1496_ = v_isSharedCheck_1544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1497_ = lean_array_get_size(v_buckets_1493_);
                crate::leanh::lean_inc_ref(v_x_1486_);
                crate::leanh::lean_inc_n(v_a_1490_, 2);
                v___x_1498_ = crate::leanh::lean_apply_1(v_x_1486_, v_a_1490_);
                v___x_1499_ = 32u64;
                v___x_1500_ = crate::leanh::lean_unbox_uint64(v___x_1498_);
                v___x_1501_ = lean_uint64_shift_right(v___x_1500_, v___x_1499_);
                v___x_1502_ = crate::leanh::lean_unbox_uint64(v___x_1498_);
                crate::leanh::lean_dec_ref(v___x_1498_);
                v_fold_1503_ = lean_uint64_xor(v___x_1502_, v___x_1501_);
                v___x_1504_ = 16u64;
                v___x_1505_ = lean_uint64_shift_right(v_fold_1503_, v___x_1504_);
                v___x_1506_ = lean_uint64_xor(v_fold_1503_, v___x_1505_);
                v___x_1507_ = lean_uint64_to_usize(v___x_1506_);
                v___x_1508_ = lean_usize_of_nat(v___x_1497_);
                v___x_1509_ = 1usize;
                v___x_1510_ = lean_usize_sub(v___x_1508_, v___x_1509_);
                v___x_1511_ = lean_usize_land(v___x_1507_, v___x_1510_);
                v_bkt_1512_ = lean_array_uget_borrowed(v_buckets_1493_, v___x_1511_);
                crate::leanh::lean_inc(v_bkt_1512_);
                crate::leanh::lean_inc_ref(v_x_1485_);
                v___x_1513_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1485_,
                    v_a_1490_,
                    v_bkt_1512_,
                );
                if v___x_1513_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_1485_);
                    v___x_1514_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1515_ = lean_nat_add(v_size_1492_, v___x_1514_);
                    crate::leanh::lean_dec(v_size_1492_);
                    crate::leanh::lean_inc(v_bkt_1512_);
                    v___x_1516_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1516_, 0, v_a_1490_);
                    crate::leanh::lean_ctor_set(v___x_1516_, 1, v_b_1491_);
                    crate::leanh::lean_ctor_set(v___x_1516_, 2, v_bkt_1512_);
                    v_buckets_x27_1517_ =
                        lean_array_uset(v_buckets_1493_, v___x_1511_, v___x_1516_);
                    v___x_1518_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1519_ = lean_nat_mul(v_size_x27_1515_, v___x_1518_);
                    v___x_1520_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1521_ = lean_nat_div(v___x_1519_, v___x_1520_);
                    crate::leanh::lean_dec(v___x_1519_);
                    v___x_1522_ = lean_array_get_size(v_buckets_x27_1517_);
                    v___x_1523_ = lean_nat_dec_le(v___x_1521_, v___x_1522_);
                    crate::leanh::lean_dec(v___x_1521_);
                    if v___x_1523_ == 0 {
                        v_val_1524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_1486_,
                            v_buckets_x27_1517_,
                        );
                        if v_isShared_1496_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1495_, 1, v_val_1524_);
                            crate::leanh::lean_ctor_set(v___x_1495_, 0, v_size_x27_1515_);
                            v___x_1526_ = v___x_1495_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1529_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1529_,
                                0,
                                v_size_x27_1515_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_val_1524_);
                            v___x_1526_ = v_reuseFailAlloc_1529_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1486_);
                        if v_isShared_1496_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1495_, 1, v_buckets_x27_1517_);
                            crate::leanh::lean_ctor_set(v___x_1495_, 0, v_size_x27_1515_);
                            v___x_1531_ = v___x_1495_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1534_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1534_,
                                0,
                                v_size_x27_1515_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1534_,
                                1,
                                v_buckets_x27_1517_,
                            );
                            v___x_1531_ = v_reuseFailAlloc_1534_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1512_);
                    crate::leanh::lean_dec_ref(v_x_1486_);
                    v___x_1535_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1536_ =
                        lean_array_uset(v_buckets_1493_, v___x_1511_, v___x_1535_);
                    v___x_1537_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_x_1485_,
                        v_a_1490_,
                        v_b_1491_,
                        v_bkt_1512_,
                    );
                    v___x_1538_ = lean_array_uset(v_buckets_x27_1536_, v___x_1511_, v___x_1537_);
                    if v_isShared_1496_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1495_, 1, v___x_1538_);
                        v___x_1540_ = v___x_1495_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_size_1492_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1538_);
                        v___x_1540_ = v_reuseFailAlloc_1543_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1527_ = crate::leanh::lean_box((v___x_1513_) as usize);
                v___x_1528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1527_);
                crate::leanh::lean_ctor_set(v___x_1528_, 1, v___x_1526_);
                return v___x_1528_;
            }
            3 => {
                v___x_1532_ = crate::leanh::lean_box((v___x_1513_) as usize);
                v___x_1533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1533_, 0, v___x_1532_);
                crate::leanh::lean_ctor_set(v___x_1533_, 1, v___x_1531_);
                return v___x_1533_;
            }
            4 => {
                v___x_1541_ = crate::leanh::lean_box((v___x_1513_) as usize);
                v___x_1542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
                crate::leanh::lean_ctor_set(v___x_1542_, 1, v___x_1540_);
                return v___x_1542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtHashMap_containsThenInsertIfNew___redArg(
    mut v_x_1545_: *mut crate::leanh::LeanObject,
    mut v_x_1546_: *mut crate::leanh::LeanObject,
    mut v_m_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_b_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: u64 = 0;
    let mut v___x_1555_: u64 = 0;
    let mut v___x_1556_: u64 = 0;
    let mut v___x_1557_: u64 = 0;
    let mut v_fold_1558_: u64 = 0;
    let mut v___x_1559_: u64 = 0;
    let mut v___x_1560_: u64 = 0;
    let mut v___x_1561_: u64 = 0;
    let mut v___x_1562_: usize = 0;
    let mut v___x_1563_: usize = 0;
    let mut v___x_1564_: usize = 0;
    let mut v___x_1565_: usize = 0;
    let mut v___x_1566_: usize = 0;
    let mut v_bkt_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v_val_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v_unused_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1550_ = crate::leanh::lean_ctor_get(v_m_1547_, 0);
                v_buckets_1551_ = crate::leanh::lean_ctor_get(v_m_1547_, 1);
                v___x_1552_ = lean_array_get_size(v_buckets_1551_);
                crate::leanh::lean_inc_ref(v_x_1546_);
                crate::leanh::lean_inc_n(v_a_1548_, 2);
                v___x_1553_ = crate::leanh::lean_apply_1(v_x_1546_, v_a_1548_);
                v___x_1554_ = 32u64;
                v___x_1555_ = crate::leanh::lean_unbox_uint64(v___x_1553_);
                v___x_1556_ = lean_uint64_shift_right(v___x_1555_, v___x_1554_);
                v___x_1557_ = crate::leanh::lean_unbox_uint64(v___x_1553_);
                crate::leanh::lean_dec_ref(v___x_1553_);
                v_fold_1558_ = lean_uint64_xor(v___x_1557_, v___x_1556_);
                v___x_1559_ = 16u64;
                v___x_1560_ = lean_uint64_shift_right(v_fold_1558_, v___x_1559_);
                v___x_1561_ = lean_uint64_xor(v_fold_1558_, v___x_1560_);
                v___x_1562_ = lean_uint64_to_usize(v___x_1561_);
                v___x_1563_ = lean_usize_of_nat(v___x_1552_);
                v___x_1564_ = 1usize;
                v___x_1565_ = lean_usize_sub(v___x_1563_, v___x_1564_);
                v___x_1566_ = lean_usize_land(v___x_1562_, v___x_1565_);
                v_bkt_1567_ = lean_array_uget_borrowed(v_buckets_1551_, v___x_1566_);
                crate::leanh::lean_inc(v_bkt_1567_);
                v___x_1568_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1545_,
                    v_a_1548_,
                    v_bkt_1567_,
                );
                if v___x_1568_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1551_);
                    crate::leanh::lean_inc(v_size_1550_);
                    v_isSharedCheck_1593_ = (!crate::leanh::lean_is_exclusive(v_m_1547_)) as u8;
                    if v_isSharedCheck_1593_ == 0 {
                        v_unused_1594_ = crate::leanh::lean_ctor_get(v_m_1547_, 1);
                        crate::leanh::lean_dec(v_unused_1594_);
                        v_unused_1595_ = crate::leanh::lean_ctor_get(v_m_1547_, 0);
                        crate::leanh::lean_dec(v_unused_1595_);
                        v___x_1570_ = v_m_1547_;
                        v_isShared_1571_ = v_isSharedCheck_1593_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1547_);
                        v___x_1570_ = crate::leanh::lean_box(0);
                        v_isShared_1571_ = v_isSharedCheck_1593_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1549_);
                    crate::leanh::lean_dec(v_a_1548_);
                    crate::leanh::lean_dec_ref(v_x_1546_);
                    v___x_1596_ = crate::leanh::lean_box((v___x_1568_) as usize);
                    v___x_1597_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1597_, 0, v___x_1596_);
                    crate::leanh::lean_ctor_set(v___x_1597_, 1, v_m_1547_);
                    return v___x_1597_;
                }
            }
            1 => {
                v___x_1572_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1573_ = lean_nat_add(v_size_1550_, v___x_1572_);
                crate::leanh::lean_dec(v_size_1550_);
                crate::leanh::lean_inc(v_bkt_1567_);
                v___x_1574_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1574_, 0, v_a_1548_);
                crate::leanh::lean_ctor_set(v___x_1574_, 1, v_b_1549_);
                crate::leanh::lean_ctor_set(v___x_1574_, 2, v_bkt_1567_);
                v_buckets_x27_1575_ = lean_array_uset(v_buckets_1551_, v___x_1566_, v___x_1574_);
                v___x_1576_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1577_ = lean_nat_mul(v_size_x27_1573_, v___x_1576_);
                v___x_1578_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1579_ = lean_nat_div(v___x_1577_, v___x_1578_);
                crate::leanh::lean_dec(v___x_1577_);
                v___x_1580_ = lean_array_get_size(v_buckets_x27_1575_);
                v___x_1581_ = lean_nat_dec_le(v___x_1579_, v___x_1580_);
                crate::leanh::lean_dec(v___x_1579_);
                if v___x_1581_ == 0 {
                    v_val_1582_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1546_,
                        v_buckets_x27_1575_,
                    );
                    if v_isShared_1571_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1570_, 1, v_val_1582_);
                        crate::leanh::lean_ctor_set(v___x_1570_, 0, v_size_x27_1573_);
                        v___x_1584_ = v___x_1570_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1587_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_size_x27_1573_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_val_1582_);
                        v___x_1584_ = v_reuseFailAlloc_1587_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1546_);
                    if v_isShared_1571_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1570_, 1, v_buckets_x27_1575_);
                        crate::leanh::lean_ctor_set(v___x_1570_, 0, v_size_x27_1573_);
                        v___x_1589_ = v___x_1570_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1592_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_size_x27_1573_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_buckets_x27_1575_);
                        v___x_1589_ = v_reuseFailAlloc_1592_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1585_ = crate::leanh::lean_box((v___x_1568_) as usize);
                v___x_1586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
                crate::leanh::lean_ctor_set(v___x_1586_, 1, v___x_1584_);
                return v___x_1586_;
            }
            3 => {
                v___x_1590_ = crate::leanh::lean_box((v___x_1568_) as usize);
                v___x_1591_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1591_, 0, v___x_1590_);
                crate::leanh::lean_ctor_set(v___x_1591_, 1, v___x_1589_);
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtHashMap_containsThenInsertIfNew(
    mut v_00_u03b1_1598_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1599_: *mut crate::leanh::LeanObject,
    mut v_x_1600_: *mut crate::leanh::LeanObject,
    mut v_x_1601_: *mut crate::leanh::LeanObject,
    mut v_inst_1602_: *mut crate::leanh::LeanObject,
    mut v_inst_1603_: *mut crate::leanh::LeanObject,
    mut v_m_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_b_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u64 = 0;
    let mut v___x_1612_: u64 = 0;
    let mut v___x_1613_: u64 = 0;
    let mut v___x_1614_: u64 = 0;
    let mut v_fold_1615_: u64 = 0;
    let mut v___x_1616_: u64 = 0;
    let mut v___x_1617_: u64 = 0;
    let mut v___x_1618_: u64 = 0;
    let mut v___x_1619_: usize = 0;
    let mut v___x_1620_: usize = 0;
    let mut v___x_1621_: usize = 0;
    let mut v___x_1622_: usize = 0;
    let mut v___x_1623_: usize = 0;
    let mut v_bkt_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v_val_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut v_unused_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1607_ = crate::leanh::lean_ctor_get(v_m_1604_, 0);
                v_buckets_1608_ = crate::leanh::lean_ctor_get(v_m_1604_, 1);
                v___x_1609_ = lean_array_get_size(v_buckets_1608_);
                crate::leanh::lean_inc_ref(v_x_1601_);
                crate::leanh::lean_inc_n(v_a_1605_, 2);
                v___x_1610_ = crate::leanh::lean_apply_1(v_x_1601_, v_a_1605_);
                v___x_1611_ = 32u64;
                v___x_1612_ = crate::leanh::lean_unbox_uint64(v___x_1610_);
                v___x_1613_ = lean_uint64_shift_right(v___x_1612_, v___x_1611_);
                v___x_1614_ = crate::leanh::lean_unbox_uint64(v___x_1610_);
                crate::leanh::lean_dec_ref(v___x_1610_);
                v_fold_1615_ = lean_uint64_xor(v___x_1614_, v___x_1613_);
                v___x_1616_ = 16u64;
                v___x_1617_ = lean_uint64_shift_right(v_fold_1615_, v___x_1616_);
                v___x_1618_ = lean_uint64_xor(v_fold_1615_, v___x_1617_);
                v___x_1619_ = lean_uint64_to_usize(v___x_1618_);
                v___x_1620_ = lean_usize_of_nat(v___x_1609_);
                v___x_1621_ = 1usize;
                v___x_1622_ = lean_usize_sub(v___x_1620_, v___x_1621_);
                v___x_1623_ = lean_usize_land(v___x_1619_, v___x_1622_);
                v_bkt_1624_ = lean_array_uget_borrowed(v_buckets_1608_, v___x_1623_);
                crate::leanh::lean_inc(v_bkt_1624_);
                v___x_1625_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1600_,
                    v_a_1605_,
                    v_bkt_1624_,
                );
                if v___x_1625_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1608_);
                    crate::leanh::lean_inc(v_size_1607_);
                    v_isSharedCheck_1650_ = (!crate::leanh::lean_is_exclusive(v_m_1604_)) as u8;
                    if v_isSharedCheck_1650_ == 0 {
                        v_unused_1651_ = crate::leanh::lean_ctor_get(v_m_1604_, 1);
                        crate::leanh::lean_dec(v_unused_1651_);
                        v_unused_1652_ = crate::leanh::lean_ctor_get(v_m_1604_, 0);
                        crate::leanh::lean_dec(v_unused_1652_);
                        v___x_1627_ = v_m_1604_;
                        v_isShared_1628_ = v_isSharedCheck_1650_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1604_);
                        v___x_1627_ = crate::leanh::lean_box(0);
                        v_isShared_1628_ = v_isSharedCheck_1650_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1606_);
                    crate::leanh::lean_dec(v_a_1605_);
                    crate::leanh::lean_dec_ref(v_x_1601_);
                    v___x_1653_ = crate::leanh::lean_box((v___x_1625_) as usize);
                    v___x_1654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1654_, 0, v___x_1653_);
                    crate::leanh::lean_ctor_set(v___x_1654_, 1, v_m_1604_);
                    return v___x_1654_;
                }
            }
            1 => {
                v___x_1629_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1630_ = lean_nat_add(v_size_1607_, v___x_1629_);
                crate::leanh::lean_dec(v_size_1607_);
                crate::leanh::lean_inc(v_bkt_1624_);
                v___x_1631_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1631_, 0, v_a_1605_);
                crate::leanh::lean_ctor_set(v___x_1631_, 1, v_b_1606_);
                crate::leanh::lean_ctor_set(v___x_1631_, 2, v_bkt_1624_);
                v_buckets_x27_1632_ = lean_array_uset(v_buckets_1608_, v___x_1623_, v___x_1631_);
                v___x_1633_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1634_ = lean_nat_mul(v_size_x27_1630_, v___x_1633_);
                v___x_1635_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1636_ = lean_nat_div(v___x_1634_, v___x_1635_);
                crate::leanh::lean_dec(v___x_1634_);
                v___x_1637_ = lean_array_get_size(v_buckets_x27_1632_);
                v___x_1638_ = lean_nat_dec_le(v___x_1636_, v___x_1637_);
                crate::leanh::lean_dec(v___x_1636_);
                if v___x_1638_ == 0 {
                    v_val_1639_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1601_,
                        v_buckets_x27_1632_,
                    );
                    if v_isShared_1628_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1627_, 1, v_val_1639_);
                        crate::leanh::lean_ctor_set(v___x_1627_, 0, v_size_x27_1630_);
                        v___x_1641_ = v___x_1627_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_size_x27_1630_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_val_1639_);
                        v___x_1641_ = v_reuseFailAlloc_1644_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1601_);
                    if v_isShared_1628_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1627_, 1, v_buckets_x27_1632_);
                        crate::leanh::lean_ctor_set(v___x_1627_, 0, v_size_x27_1630_);
                        v___x_1646_ = v___x_1627_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_size_x27_1630_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_buckets_x27_1632_);
                        v___x_1646_ = v_reuseFailAlloc_1649_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1642_ = crate::leanh::lean_box((v___x_1625_) as usize);
                v___x_1643_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1643_, 0, v___x_1642_);
                crate::leanh::lean_ctor_set(v___x_1643_, 1, v___x_1641_);
                return v___x_1643_;
            }
            3 => {
                v___x_1647_ = crate::leanh::lean_box((v___x_1625_) as usize);
                v___x_1648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1648_, 0, v___x_1647_);
                crate::leanh::lean_ctor_set(v___x_1648_, 1, v___x_1646_);
                return v___x_1648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtHashMap_getThenInsertIfNew_x3f___redArg(
    mut v_x_1655_: *mut crate::leanh::LeanObject,
    mut v_x_1656_: *mut crate::leanh::LeanObject,
    mut v_m_1657_: *mut crate::leanh::LeanObject,
    mut v_a_1658_: *mut crate::leanh::LeanObject,
    mut v_b_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u64 = 0;
    let mut v___x_1665_: u64 = 0;
    let mut v___x_1666_: u64 = 0;
    let mut v___x_1667_: u64 = 0;
    let mut v_fold_1668_: u64 = 0;
    let mut v___x_1669_: u64 = 0;
    let mut v___x_1670_: u64 = 0;
    let mut v___x_1671_: u64 = 0;
    let mut v___x_1672_: usize = 0;
    let mut v___x_1673_: usize = 0;
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: usize = 0;
    let mut v_bkt_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1681_: u8 = 0;
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: u8 = 0;
    let mut v_val_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1701_: u8 = 0;
    let mut v_unused_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1660_ = crate::leanh::lean_ctor_get(v_m_1657_, 0);
                v_buckets_1661_ = crate::leanh::lean_ctor_get(v_m_1657_, 1);
                v___x_1662_ = lean_array_get_size(v_buckets_1661_);
                crate::leanh::lean_inc_ref(v_x_1656_);
                crate::leanh::lean_inc_n(v_a_1658_, 2);
                v___x_1663_ = crate::leanh::lean_apply_1(v_x_1656_, v_a_1658_);
                v___x_1664_ = 32u64;
                v___x_1665_ = crate::leanh::lean_unbox_uint64(v___x_1663_);
                v___x_1666_ = lean_uint64_shift_right(v___x_1665_, v___x_1664_);
                v___x_1667_ = crate::leanh::lean_unbox_uint64(v___x_1663_);
                crate::leanh::lean_dec_ref(v___x_1663_);
                v_fold_1668_ = lean_uint64_xor(v___x_1667_, v___x_1666_);
                v___x_1669_ = 16u64;
                v___x_1670_ = lean_uint64_shift_right(v_fold_1668_, v___x_1669_);
                v___x_1671_ = lean_uint64_xor(v_fold_1668_, v___x_1670_);
                v___x_1672_ = lean_uint64_to_usize(v___x_1671_);
                v___x_1673_ = lean_usize_of_nat(v___x_1662_);
                v___x_1674_ = 1usize;
                v___x_1675_ = lean_usize_sub(v___x_1673_, v___x_1674_);
                v___x_1676_ = lean_usize_land(v___x_1672_, v___x_1675_);
                v_bkt_1677_ = lean_array_uget_borrowed(v_buckets_1661_, v___x_1676_);
                crate::leanh::lean_inc(v_bkt_1677_);
                v___x_1678_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_1655_,
                    v_a_1658_,
                    v_bkt_1677_,
                );
                if crate::leanh::lean_obj_tag(v___x_1678_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1661_);
                    crate::leanh::lean_inc(v_size_1660_);
                    v_isSharedCheck_1701_ = (!crate::leanh::lean_is_exclusive(v_m_1657_)) as u8;
                    if v_isSharedCheck_1701_ == 0 {
                        v_unused_1702_ = crate::leanh::lean_ctor_get(v_m_1657_, 1);
                        crate::leanh::lean_dec(v_unused_1702_);
                        v_unused_1703_ = crate::leanh::lean_ctor_get(v_m_1657_, 0);
                        crate::leanh::lean_dec(v_unused_1703_);
                        v___x_1680_ = v_m_1657_;
                        v_isShared_1681_ = v_isSharedCheck_1701_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1657_);
                        v___x_1680_ = crate::leanh::lean_box(0);
                        v_isShared_1681_ = v_isSharedCheck_1701_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1659_);
                    crate::leanh::lean_dec(v_a_1658_);
                    crate::leanh::lean_dec_ref(v_x_1656_);
                    v___x_1704_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1704_, 0, v___x_1678_);
                    crate::leanh::lean_ctor_set(v___x_1704_, 1, v_m_1657_);
                    return v___x_1704_;
                }
            }
            1 => {
                v___x_1682_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1683_ = lean_nat_add(v_size_1660_, v___x_1682_);
                crate::leanh::lean_dec(v_size_1660_);
                crate::leanh::lean_inc(v_bkt_1677_);
                v___x_1684_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1684_, 0, v_a_1658_);
                crate::leanh::lean_ctor_set(v___x_1684_, 1, v_b_1659_);
                crate::leanh::lean_ctor_set(v___x_1684_, 2, v_bkt_1677_);
                v_buckets_x27_1685_ = lean_array_uset(v_buckets_1661_, v___x_1676_, v___x_1684_);
                v___x_1686_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1687_ = lean_nat_mul(v_size_x27_1683_, v___x_1686_);
                v___x_1688_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1689_ = lean_nat_div(v___x_1687_, v___x_1688_);
                crate::leanh::lean_dec(v___x_1687_);
                v___x_1690_ = lean_array_get_size(v_buckets_x27_1685_);
                v___x_1691_ = lean_nat_dec_le(v___x_1689_, v___x_1690_);
                crate::leanh::lean_dec(v___x_1689_);
                if v___x_1691_ == 0 {
                    v_val_1692_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1656_,
                        v_buckets_x27_1685_,
                    );
                    if v_isShared_1681_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1680_, 1, v_val_1692_);
                        crate::leanh::lean_ctor_set(v___x_1680_, 0, v_size_x27_1683_);
                        v___x_1694_ = v___x_1680_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_size_x27_1683_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_val_1692_);
                        v___x_1694_ = v_reuseFailAlloc_1696_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1656_);
                    if v_isShared_1681_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1680_, 1, v_buckets_x27_1685_);
                        crate::leanh::lean_ctor_set(v___x_1680_, 0, v_size_x27_1683_);
                        v___x_1698_ = v___x_1680_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_size_x27_1683_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_buckets_x27_1685_);
                        v___x_1698_ = v_reuseFailAlloc_1700_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1695_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1695_, 0, v___x_1678_);
                crate::leanh::lean_ctor_set(v___x_1695_, 1, v___x_1694_);
                return v___x_1695_;
            }
            3 => {
                v___x_1699_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1699_, 0, v___x_1678_);
                crate::leanh::lean_ctor_set(v___x_1699_, 1, v___x_1698_);
                return v___x_1699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtHashMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_1705_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
    mut v_x_1708_: *mut crate::leanh::LeanObject,
    mut v_inst_1709_: *mut crate::leanh::LeanObject,
    mut v_inst_1710_: *mut crate::leanh::LeanObject,
    mut v_m_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_b_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: u64 = 0;
    let mut v___x_1719_: u64 = 0;
    let mut v___x_1720_: u64 = 0;
    let mut v___x_1721_: u64 = 0;
    let mut v_fold_1722_: u64 = 0;
    let mut v___x_1723_: u64 = 0;
    let mut v___x_1724_: u64 = 0;
    let mut v___x_1725_: u64 = 0;
    let mut v___x_1726_: usize = 0;
    let mut v___x_1727_: usize = 0;
    let mut v___x_1728_: usize = 0;
    let mut v___x_1729_: usize = 0;
    let mut v___x_1730_: usize = 0;
    let mut v_bkt_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1735_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: u8 = 0;
    let mut v_val_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_unused_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1714_ = crate::leanh::lean_ctor_get(v_m_1711_, 0);
                v_buckets_1715_ = crate::leanh::lean_ctor_get(v_m_1711_, 1);
                v___x_1716_ = lean_array_get_size(v_buckets_1715_);
                crate::leanh::lean_inc_ref(v_x_1708_);
                crate::leanh::lean_inc_n(v_a_1712_, 2);
                v___x_1717_ = crate::leanh::lean_apply_1(v_x_1708_, v_a_1712_);
                v___x_1718_ = 32u64;
                v___x_1719_ = crate::leanh::lean_unbox_uint64(v___x_1717_);
                v___x_1720_ = lean_uint64_shift_right(v___x_1719_, v___x_1718_);
                v___x_1721_ = crate::leanh::lean_unbox_uint64(v___x_1717_);
                crate::leanh::lean_dec_ref(v___x_1717_);
                v_fold_1722_ = lean_uint64_xor(v___x_1721_, v___x_1720_);
                v___x_1723_ = 16u64;
                v___x_1724_ = lean_uint64_shift_right(v_fold_1722_, v___x_1723_);
                v___x_1725_ = lean_uint64_xor(v_fold_1722_, v___x_1724_);
                v___x_1726_ = lean_uint64_to_usize(v___x_1725_);
                v___x_1727_ = lean_usize_of_nat(v___x_1716_);
                v___x_1728_ = 1usize;
                v___x_1729_ = lean_usize_sub(v___x_1727_, v___x_1728_);
                v___x_1730_ = lean_usize_land(v___x_1726_, v___x_1729_);
                v_bkt_1731_ = lean_array_uget_borrowed(v_buckets_1715_, v___x_1730_);
                crate::leanh::lean_inc(v_bkt_1731_);
                v___x_1732_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_1707_,
                    v_a_1712_,
                    v_bkt_1731_,
                );
                if crate::leanh::lean_obj_tag(v___x_1732_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1715_);
                    crate::leanh::lean_inc(v_size_1714_);
                    v_isSharedCheck_1755_ = (!crate::leanh::lean_is_exclusive(v_m_1711_)) as u8;
                    if v_isSharedCheck_1755_ == 0 {
                        v_unused_1756_ = crate::leanh::lean_ctor_get(v_m_1711_, 1);
                        crate::leanh::lean_dec(v_unused_1756_);
                        v_unused_1757_ = crate::leanh::lean_ctor_get(v_m_1711_, 0);
                        crate::leanh::lean_dec(v_unused_1757_);
                        v___x_1734_ = v_m_1711_;
                        v_isShared_1735_ = v_isSharedCheck_1755_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1711_);
                        v___x_1734_ = crate::leanh::lean_box(0);
                        v_isShared_1735_ = v_isSharedCheck_1755_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1713_);
                    crate::leanh::lean_dec(v_a_1712_);
                    crate::leanh::lean_dec_ref(v_x_1708_);
                    v___x_1758_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1732_);
                    crate::leanh::lean_ctor_set(v___x_1758_, 1, v_m_1711_);
                    return v___x_1758_;
                }
            }
            1 => {
                v___x_1736_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1737_ = lean_nat_add(v_size_1714_, v___x_1736_);
                crate::leanh::lean_dec(v_size_1714_);
                crate::leanh::lean_inc(v_bkt_1731_);
                v___x_1738_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1738_, 0, v_a_1712_);
                crate::leanh::lean_ctor_set(v___x_1738_, 1, v_b_1713_);
                crate::leanh::lean_ctor_set(v___x_1738_, 2, v_bkt_1731_);
                v_buckets_x27_1739_ = lean_array_uset(v_buckets_1715_, v___x_1730_, v___x_1738_);
                v___x_1740_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1741_ = lean_nat_mul(v_size_x27_1737_, v___x_1740_);
                v___x_1742_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1743_ = lean_nat_div(v___x_1741_, v___x_1742_);
                crate::leanh::lean_dec(v___x_1741_);
                v___x_1744_ = lean_array_get_size(v_buckets_x27_1739_);
                v___x_1745_ = lean_nat_dec_le(v___x_1743_, v___x_1744_);
                crate::leanh::lean_dec(v___x_1743_);
                if v___x_1745_ == 0 {
                    v_val_1746_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1708_,
                        v_buckets_x27_1739_,
                    );
                    if v_isShared_1735_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1734_, 1, v_val_1746_);
                        crate::leanh::lean_ctor_set(v___x_1734_, 0, v_size_x27_1737_);
                        v___x_1748_ = v___x_1734_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_size_x27_1737_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_val_1746_);
                        v___x_1748_ = v_reuseFailAlloc_1750_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1708_);
                    if v_isShared_1735_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1734_, 1, v_buckets_x27_1739_);
                        crate::leanh::lean_ctor_set(v___x_1734_, 0, v_size_x27_1737_);
                        v___x_1752_ = v___x_1734_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1754_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_size_x27_1737_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_buckets_x27_1739_);
                        v___x_1752_ = v_reuseFailAlloc_1754_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1749_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1749_, 0, v___x_1732_);
                crate::leanh::lean_ctor_set(v___x_1749_, 1, v___x_1748_);
                return v___x_1749_;
            }
            3 => {
                v___x_1753_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1732_);
                crate::leanh::lean_ctor_set(v___x_1753_, 1, v___x_1752_);
                return v___x_1753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtHashMap_get_x3f___redArg(
    mut v_x_1759_: *mut crate::leanh::LeanObject,
    mut v_x_1760_: *mut crate::leanh::LeanObject,
    mut v_m_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_1759_, v_x_1760_, v_m_1761_, v_a_1762_,
    );
    return v___x_1763_;
}
pub unsafe fn l_Std_ExtHashMap_get_x3f___redArg___boxed(
    mut v_x_1764_: *mut crate::leanh::LeanObject,
    mut v_x_1765_: *mut crate::leanh::LeanObject,
    mut v_m_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Std_ExtHashMap_get_x3f___redArg(v_x_1764_, v_x_1765_, v_m_1766_, v_a_1767_);
    crate::leanh::lean_dec(v_m_1766_);
    return v_res_1768_;
}
pub unsafe fn l_Std_ExtHashMap_get_x3f(
    mut v_00_u03b1_1769_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1770_: *mut crate::leanh::LeanObject,
    mut v_x_1771_: *mut crate::leanh::LeanObject,
    mut v_x_1772_: *mut crate::leanh::LeanObject,
    mut v_inst_1773_: *mut crate::leanh::LeanObject,
    mut v_inst_1774_: *mut crate::leanh::LeanObject,
    mut v_m_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_1771_, v_x_1772_, v_m_1775_, v_a_1776_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Std_ExtHashMap_get_x3f___boxed(
    mut v_00_u03b1_1778_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1779_: *mut crate::leanh::LeanObject,
    mut v_x_1780_: *mut crate::leanh::LeanObject,
    mut v_x_1781_: *mut crate::leanh::LeanObject,
    mut v_inst_1782_: *mut crate::leanh::LeanObject,
    mut v_inst_1783_: *mut crate::leanh::LeanObject,
    mut v_m_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Std_ExtHashMap_get_x3f(
        v_00_u03b1_1778_,
        v_00_u03b2_1779_,
        v_x_1780_,
        v_x_1781_,
        v_inst_1782_,
        v_inst_1783_,
        v_m_1784_,
        v_a_1785_,
    );
    crate::leanh::lean_dec(v_m_1784_);
    return v_res_1786_;
}
pub unsafe fn l_Std_ExtHashMap_contains___redArg(
    mut v_x_1787_: *mut crate::leanh::LeanObject,
    mut v_x_1788_: *mut crate::leanh::LeanObject,
    mut v_m_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1791_: u8 = 0;
    v___x_1791_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_1787_, v_x_1788_, v_m_1789_, v_a_1790_,
    );
    return v___x_1791_;
}
pub unsafe fn l_Std_ExtHashMap_contains___redArg___boxed(
    mut v_x_1792_: *mut crate::leanh::LeanObject,
    mut v_x_1793_: *mut crate::leanh::LeanObject,
    mut v_m_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1796_: u8 = 0;
    let mut v_r_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Std_ExtHashMap_contains___redArg(v_x_1792_, v_x_1793_, v_m_1794_, v_a_1795_);
    crate::leanh::lean_dec(v_m_1794_);
    v_r_1797_ = crate::leanh::lean_box((v_res_1796_) as usize);
    return v_r_1797_;
}
pub unsafe fn l_Std_ExtHashMap_contains(
    mut v_00_u03b1_1798_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1799_: *mut crate::leanh::LeanObject,
    mut v_x_1800_: *mut crate::leanh::LeanObject,
    mut v_x_1801_: *mut crate::leanh::LeanObject,
    mut v_inst_1802_: *mut crate::leanh::LeanObject,
    mut v_inst_1803_: *mut crate::leanh::LeanObject,
    mut v_m_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1806_: u8 = 0;
    v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_1800_, v_x_1801_, v_m_1804_, v_a_1805_,
    );
    return v___x_1806_;
}
pub unsafe fn l_Std_ExtHashMap_contains___boxed(
    mut v_00_u03b1_1807_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1808_: *mut crate::leanh::LeanObject,
    mut v_x_1809_: *mut crate::leanh::LeanObject,
    mut v_x_1810_: *mut crate::leanh::LeanObject,
    mut v_inst_1811_: *mut crate::leanh::LeanObject,
    mut v_inst_1812_: *mut crate::leanh::LeanObject,
    mut v_m_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1815_: u8 = 0;
    let mut v_r_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1815_ = l_Std_ExtHashMap_contains(
        v_00_u03b1_1807_,
        v_00_u03b2_1808_,
        v_x_1809_,
        v_x_1810_,
        v_inst_1811_,
        v_inst_1812_,
        v_m_1813_,
        v_a_1814_,
    );
    crate::leanh::lean_dec(v_m_1813_);
    v_r_1816_ = crate::leanh::lean_box((v_res_1815_) as usize);
    return v_r_1816_;
}
pub unsafe fn l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1817_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1818_: *mut crate::leanh::LeanObject,
    mut v_inst_1819_: *mut crate::leanh::LeanObject,
    mut v_inst_1820_: *mut crate::leanh::LeanObject,
    mut v_inst_1821_: *mut crate::leanh::LeanObject,
    mut v_inst_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1823_ = crate::leanh::lean_box(0);
    return v___x_1823_;
}
pub unsafe fn l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(
    mut v_00_u03b1_1824_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1825_: *mut crate::leanh::LeanObject,
    mut v_inst_1826_: *mut crate::leanh::LeanObject,
    mut v_inst_1827_: *mut crate::leanh::LeanObject,
    mut v_inst_1828_: *mut crate::leanh::LeanObject,
    mut v_inst_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(
        v_00_u03b1_1824_,
        v_00_u03b2_1825_,
        v_inst_1826_,
        v_inst_1827_,
        v_inst_1828_,
        v_inst_1829_,
    );
    crate::leanh::lean_dec_ref(v_inst_1827_);
    crate::leanh::lean_dec_ref(v_inst_1826_);
    return v_res_1830_;
}
pub unsafe fn l_Std_ExtHashMap_instDecidableMem___redArg(
    mut v_inst_1831_: *mut crate::leanh::LeanObject,
    mut v_inst_1832_: *mut crate::leanh::LeanObject,
    mut v_m_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1835_: u8 = 0;
    v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_1831_,
        v_inst_1832_,
        v_m_1833_,
        v_a_1834_,
    );
    return v___x_1835_;
}
pub unsafe fn l_Std_ExtHashMap_instDecidableMem___redArg___boxed(
    mut v_inst_1836_: *mut crate::leanh::LeanObject,
    mut v_inst_1837_: *mut crate::leanh::LeanObject,
    mut v_m_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1840_: u8 = 0;
    let mut v_r_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1840_ = l_Std_ExtHashMap_instDecidableMem___redArg(
        v_inst_1836_,
        v_inst_1837_,
        v_m_1838_,
        v_a_1839_,
    );
    crate::leanh::lean_dec(v_m_1838_);
    v_r_1841_ = crate::leanh::lean_box((v_res_1840_) as usize);
    return v_r_1841_;
}
pub unsafe fn l_Std_ExtHashMap_instDecidableMem(
    mut v_00_u03b1_1842_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1843_: *mut crate::leanh::LeanObject,
    mut v_inst_1844_: *mut crate::leanh::LeanObject,
    mut v_inst_1845_: *mut crate::leanh::LeanObject,
    mut v_inst_1846_: *mut crate::leanh::LeanObject,
    mut v_inst_1847_: *mut crate::leanh::LeanObject,
    mut v_m_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1850_: u8 = 0;
    v___x_1850_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_1844_,
        v_inst_1845_,
        v_m_1848_,
        v_a_1849_,
    );
    return v___x_1850_;
}
pub unsafe fn l_Std_ExtHashMap_instDecidableMem___boxed(
    mut v_00_u03b1_1851_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1852_: *mut crate::leanh::LeanObject,
    mut v_inst_1853_: *mut crate::leanh::LeanObject,
    mut v_inst_1854_: *mut crate::leanh::LeanObject,
    mut v_inst_1855_: *mut crate::leanh::LeanObject,
    mut v_inst_1856_: *mut crate::leanh::LeanObject,
    mut v_m_1857_: *mut crate::leanh::LeanObject,
    mut v_a_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1859_: u8 = 0;
    let mut v_r_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1859_ = l_Std_ExtHashMap_instDecidableMem(
        v_00_u03b1_1851_,
        v_00_u03b2_1852_,
        v_inst_1853_,
        v_inst_1854_,
        v_inst_1855_,
        v_inst_1856_,
        v_m_1857_,
        v_a_1858_,
    );
    crate::leanh::lean_dec(v_m_1857_);
    v_r_1860_ = crate::leanh::lean_box((v_res_1859_) as usize);
    return v_r_1860_;
}
pub unsafe fn l_Std_ExtHashMap_get___redArg(
    mut v_x_1861_: *mut crate::leanh::LeanObject,
    mut v_x_1862_: *mut crate::leanh::LeanObject,
    mut v_m_1863_: *mut crate::leanh::LeanObject,
    mut v_a_1864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_1861_, v_x_1862_, v_m_1863_, v_a_1864_,
    );
    return v___x_1865_;
}
pub unsafe fn l_Std_ExtHashMap_get___redArg___boxed(
    mut v_x_1866_: *mut crate::leanh::LeanObject,
    mut v_x_1867_: *mut crate::leanh::LeanObject,
    mut v_m_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1870_ = l_Std_ExtHashMap_get___redArg(v_x_1866_, v_x_1867_, v_m_1868_, v_a_1869_);
    crate::leanh::lean_dec(v_m_1868_);
    return v_res_1870_;
}
pub unsafe fn l_Std_ExtHashMap_get(
    mut v_00_u03b1_1871_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1872_: *mut crate::leanh::LeanObject,
    mut v_x_1873_: *mut crate::leanh::LeanObject,
    mut v_x_1874_: *mut crate::leanh::LeanObject,
    mut v_inst_1875_: *mut crate::leanh::LeanObject,
    mut v_inst_1876_: *mut crate::leanh::LeanObject,
    mut v_m_1877_: *mut crate::leanh::LeanObject,
    mut v_a_1878_: *mut crate::leanh::LeanObject,
    mut v_h_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_1873_, v_x_1874_, v_m_1877_, v_a_1878_,
    );
    return v___x_1880_;
}
pub unsafe fn l_Std_ExtHashMap_get___boxed(
    mut v_00_u03b1_1881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1882_: *mut crate::leanh::LeanObject,
    mut v_x_1883_: *mut crate::leanh::LeanObject,
    mut v_x_1884_: *mut crate::leanh::LeanObject,
    mut v_inst_1885_: *mut crate::leanh::LeanObject,
    mut v_inst_1886_: *mut crate::leanh::LeanObject,
    mut v_m_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_h_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1890_ = l_Std_ExtHashMap_get(
        v_00_u03b1_1881_,
        v_00_u03b2_1882_,
        v_x_1883_,
        v_x_1884_,
        v_inst_1885_,
        v_inst_1886_,
        v_m_1887_,
        v_a_1888_,
        v_h_1889_,
    );
    crate::leanh::lean_dec(v_m_1887_);
    return v_res_1890_;
}
pub unsafe fn l_Std_ExtHashMap_getD___redArg(
    mut v_x_1891_: *mut crate::leanh::LeanObject,
    mut v_x_1892_: *mut crate::leanh::LeanObject,
    mut v_m_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_fallback_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_x_1891_,
        v_x_1892_,
        v_m_1893_,
        v_a_1894_,
        v_fallback_1895_,
    );
    return v___x_1896_;
}
pub unsafe fn l_Std_ExtHashMap_getD___redArg___boxed(
    mut v_x_1897_: *mut crate::leanh::LeanObject,
    mut v_x_1898_: *mut crate::leanh::LeanObject,
    mut v_m_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
    mut v_fallback_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Std_ExtHashMap_getD___redArg(
        v_x_1897_,
        v_x_1898_,
        v_m_1899_,
        v_a_1900_,
        v_fallback_1901_,
    );
    crate::leanh::lean_dec(v_fallback_1901_);
    crate::leanh::lean_dec(v_m_1899_);
    return v_res_1902_;
}
pub unsafe fn l_Std_ExtHashMap_getD(
    mut v_00_u03b1_1903_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1904_: *mut crate::leanh::LeanObject,
    mut v_x_1905_: *mut crate::leanh::LeanObject,
    mut v_x_1906_: *mut crate::leanh::LeanObject,
    mut v_inst_1907_: *mut crate::leanh::LeanObject,
    mut v_inst_1908_: *mut crate::leanh::LeanObject,
    mut v_m_1909_: *mut crate::leanh::LeanObject,
    mut v_a_1910_: *mut crate::leanh::LeanObject,
    mut v_fallback_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_x_1905_,
        v_x_1906_,
        v_m_1909_,
        v_a_1910_,
        v_fallback_1911_,
    );
    return v___x_1912_;
}
pub unsafe fn l_Std_ExtHashMap_getD___boxed(
    mut v_00_u03b1_1913_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1914_: *mut crate::leanh::LeanObject,
    mut v_x_1915_: *mut crate::leanh::LeanObject,
    mut v_x_1916_: *mut crate::leanh::LeanObject,
    mut v_inst_1917_: *mut crate::leanh::LeanObject,
    mut v_inst_1918_: *mut crate::leanh::LeanObject,
    mut v_m_1919_: *mut crate::leanh::LeanObject,
    mut v_a_1920_: *mut crate::leanh::LeanObject,
    mut v_fallback_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Std_ExtHashMap_getD(
        v_00_u03b1_1913_,
        v_00_u03b2_1914_,
        v_x_1915_,
        v_x_1916_,
        v_inst_1917_,
        v_inst_1918_,
        v_m_1919_,
        v_a_1920_,
        v_fallback_1921_,
    );
    crate::leanh::lean_dec(v_fallback_1921_);
    crate::leanh::lean_dec(v_m_1919_);
    return v_res_1922_;
}
pub unsafe fn l_Std_ExtHashMap_get_x21___redArg(
    mut v_x_1923_: *mut crate::leanh::LeanObject,
    mut v_x_1924_: *mut crate::leanh::LeanObject,
    mut v_inst_1925_: *mut crate::leanh::LeanObject,
    mut v_m_1926_: *mut crate::leanh::LeanObject,
    mut v_a_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_x_1923_,
        v_x_1924_,
        v_inst_1925_,
        v_m_1926_,
        v_a_1927_,
    );
    return v___x_1928_;
}
pub unsafe fn l_Std_ExtHashMap_get_x21___redArg___boxed(
    mut v_x_1929_: *mut crate::leanh::LeanObject,
    mut v_x_1930_: *mut crate::leanh::LeanObject,
    mut v_inst_1931_: *mut crate::leanh::LeanObject,
    mut v_m_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ =
        l_Std_ExtHashMap_get_x21___redArg(v_x_1929_, v_x_1930_, v_inst_1931_, v_m_1932_, v_a_1933_);
    crate::leanh::lean_dec(v_m_1932_);
    crate::leanh::lean_dec(v_inst_1931_);
    return v_res_1934_;
}
pub unsafe fn l_Std_ExtHashMap_get_x21(
    mut v_00_u03b1_1935_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1936_: *mut crate::leanh::LeanObject,
    mut v_x_1937_: *mut crate::leanh::LeanObject,
    mut v_x_1938_: *mut crate::leanh::LeanObject,
    mut v_inst_1939_: *mut crate::leanh::LeanObject,
    mut v_inst_1940_: *mut crate::leanh::LeanObject,
    mut v_inst_1941_: *mut crate::leanh::LeanObject,
    mut v_m_1942_: *mut crate::leanh::LeanObject,
    mut v_a_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_x_1937_,
        v_x_1938_,
        v_inst_1941_,
        v_m_1942_,
        v_a_1943_,
    );
    return v___x_1944_;
}
pub unsafe fn l_Std_ExtHashMap_get_x21___boxed(
    mut v_00_u03b1_1945_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1946_: *mut crate::leanh::LeanObject,
    mut v_x_1947_: *mut crate::leanh::LeanObject,
    mut v_x_1948_: *mut crate::leanh::LeanObject,
    mut v_inst_1949_: *mut crate::leanh::LeanObject,
    mut v_inst_1950_: *mut crate::leanh::LeanObject,
    mut v_inst_1951_: *mut crate::leanh::LeanObject,
    mut v_m_1952_: *mut crate::leanh::LeanObject,
    mut v_a_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1954_ = l_Std_ExtHashMap_get_x21(
        v_00_u03b1_1945_,
        v_00_u03b2_1946_,
        v_x_1947_,
        v_x_1948_,
        v_inst_1949_,
        v_inst_1950_,
        v_inst_1951_,
        v_m_1952_,
        v_a_1953_,
    );
    crate::leanh::lean_dec(v_m_1952_);
    crate::leanh::lean_dec(v_inst_1951_);
    return v_res_1954_;
}
pub unsafe fn l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(
    mut v_inst_1955_: *mut crate::leanh::LeanObject,
    mut v_inst_1956_: *mut crate::leanh::LeanObject,
    mut v_m_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
    mut v_h_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_1955_,
        v_inst_1956_,
        v_m_1957_,
        v_a_1958_,
    );
    return v___x_1960_;
}
pub unsafe fn l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed(
    mut v_inst_1961_: *mut crate::leanh::LeanObject,
    mut v_inst_1962_: *mut crate::leanh::LeanObject,
    mut v_m_1963_: *mut crate::leanh::LeanObject,
    mut v_a_1964_: *mut crate::leanh::LeanObject,
    mut v_h_1965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(
        v_inst_1961_,
        v_inst_1962_,
        v_m_1963_,
        v_a_1964_,
        v_h_1965_,
    );
    crate::leanh::lean_dec(v_m_1963_);
    return v_res_1966_;
}
pub unsafe fn l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(
    mut v_inst_1967_: *mut crate::leanh::LeanObject,
    mut v_inst_1968_: *mut crate::leanh::LeanObject,
    mut v_m_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_1967_,
        v_inst_1968_,
        v_m_1969_,
        v_a_1970_,
    );
    return v___x_1971_;
}
pub unsafe fn l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed(
    mut v_inst_1972_: *mut crate::leanh::LeanObject,
    mut v_inst_1973_: *mut crate::leanh::LeanObject,
    mut v_m_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(
        v_inst_1972_,
        v_inst_1973_,
        v_m_1974_,
        v_a_1975_,
    );
    crate::leanh::lean_dec(v_m_1974_);
    return v_res_1976_;
}
pub unsafe fn l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(
    mut v_inst_1977_: *mut crate::leanh::LeanObject,
    mut v_inst_1978_: *mut crate::leanh::LeanObject,
    mut v_inst_1979_: *mut crate::leanh::LeanObject,
    mut v_m_1980_: *mut crate::leanh::LeanObject,
    mut v_a_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_inst_1977_,
        v_inst_1978_,
        v_inst_1979_,
        v_m_1980_,
        v_a_1981_,
    );
    return v___x_1982_;
}
pub unsafe fn l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed(
    mut v_inst_1983_: *mut crate::leanh::LeanObject,
    mut v_inst_1984_: *mut crate::leanh::LeanObject,
    mut v_inst_1985_: *mut crate::leanh::LeanObject,
    mut v_m_1986_: *mut crate::leanh::LeanObject,
    mut v_a_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1988_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(
        v_inst_1983_,
        v_inst_1984_,
        v_inst_1985_,
        v_m_1986_,
        v_a_1987_,
    );
    crate::leanh::lean_dec(v_m_1986_);
    crate::leanh::lean_dec(v_inst_1985_);
    return v_res_1988_;
}
pub unsafe fn l_Std_ExtHashMap_instGetElem_x3fMem___redArg(
    mut v_inst_1989_: *mut crate::leanh::LeanObject,
    mut v_inst_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1990_, 2);
    crate::leanh::lean_inc_ref_n(v_inst_1989_, 2);
    v___f_1991_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1991_, 0, v_inst_1989_);
    crate::leanh::lean_closure_set(v___f_1991_, 1, v_inst_1990_);
    v___f_1992_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1992_, 0, v_inst_1989_);
    crate::leanh::lean_closure_set(v___f_1992_, 1, v_inst_1990_);
    v___f_1993_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1993_, 0, v_inst_1989_);
    crate::leanh::lean_closure_set(v___f_1993_, 1, v_inst_1990_);
    v___x_1994_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1994_, 0, v___f_1991_);
    crate::leanh::lean_ctor_set(v___x_1994_, 1, v___f_1992_);
    crate::leanh::lean_ctor_set(v___x_1994_, 2, v___f_1993_);
    return v___x_1994_;
}
pub unsafe fn l_Std_ExtHashMap_instGetElem_x3fMem(
    mut v_00_u03b1_1995_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1996_: *mut crate::leanh::LeanObject,
    mut v_inst_1997_: *mut crate::leanh::LeanObject,
    mut v_inst_1998_: *mut crate::leanh::LeanObject,
    mut v_inst_1999_: *mut crate::leanh::LeanObject,
    mut v_inst_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg(v_inst_1997_, v_inst_1998_);
    return v___x_2001_;
}
pub unsafe fn l_Std_ExtHashMap_getKey_x3f___redArg(
    mut v_x_2002_: *mut crate::leanh::LeanObject,
    mut v_x_2003_: *mut crate::leanh::LeanObject,
    mut v_m_2004_: *mut crate::leanh::LeanObject,
    mut v_a_2005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2006_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_2002_, v_x_2003_, v_m_2004_, v_a_2005_,
    );
    return v___x_2006_;
}
pub unsafe fn l_Std_ExtHashMap_getKey_x3f___redArg___boxed(
    mut v_x_2007_: *mut crate::leanh::LeanObject,
    mut v_x_2008_: *mut crate::leanh::LeanObject,
    mut v_m_2009_: *mut crate::leanh::LeanObject,
    mut v_a_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2011_ = l_Std_ExtHashMap_getKey_x3f___redArg(v_x_2007_, v_x_2008_, v_m_2009_, v_a_2010_);
    crate::leanh::lean_dec(v_m_2009_);
    return v_res_2011_;
}
pub unsafe fn l_Std_ExtHashMap_getKey_x3f(
    mut v_00_u03b1_2012_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2013_: *mut crate::leanh::LeanObject,
    mut v_x_2014_: *mut crate::leanh::LeanObject,
    mut v_x_2015_: *mut crate::leanh::LeanObject,
    mut v_inst_2016_: *mut crate::leanh::LeanObject,
    mut v_inst_2017_: *mut crate::leanh::LeanObject,
    mut v_m_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_2014_, v_x_2015_, v_m_2018_, v_a_2019_,
    );
    return v___x_2020_;
}
pub unsafe fn l_Std_ExtHashMap_getKey_x3f___boxed(
    mut v_00_u03b1_2021_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2022_: *mut crate::leanh::LeanObject,
    mut v_x_2023_: *mut crate::leanh::LeanObject,
    mut v_x_2024_: *mut crate::leanh::LeanObject,
    mut v_inst_2025_: *mut crate::leanh::LeanObject,
    mut v_inst_2026_: *mut crate::leanh::LeanObject,
    mut v_m_2027_: *mut crate::leanh::LeanObject,
    mut v_a_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2029_ = l_Std_ExtHashMap_getKey_x3f(
        v_00_u03b1_2021_,
        v_00_u03b2_2022_,
        v_x_2023_,
        v_x_2024_,
        v_inst_2025_,
        v_inst_2026_,
        v_m_2027_,
        v_a_2028_,
    );
    crate::leanh::lean_dec(v_m_2027_);
    return v_res_2029_;
}
pub unsafe fn l_Std_ExtHashMap_getKey___redArg(
    mut v_x_2030_: *mut crate::leanh::LeanObject,
    mut v_x_2031_: *mut crate::leanh::LeanObject,
    mut v_m_2032_: *mut crate::leanh::LeanObject,
    mut v_a_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_2030_, v_x_2031_, v_m_2032_, v_a_2033_,
    );
    return v___x_2034_;
}
pub unsafe fn l_Std_ExtHashMap_getKey___redArg___boxed(
    mut v_x_2035_: *mut crate::leanh::LeanObject,
    mut v_x_2036_: *mut crate::leanh::LeanObject,
    mut v_m_2037_: *mut crate::leanh::LeanObject,
    mut v_a_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Std_ExtHashMap_getKey___redArg(v_x_2035_, v_x_2036_, v_m_2037_, v_a_2038_);
    crate::leanh::lean_dec(v_m_2037_);
    return v_res_2039_;
}
pub unsafe fn l_Std_ExtHashMap_getKey(
    mut v_00_u03b1_2040_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2041_: *mut crate::leanh::LeanObject,
    mut v_x_2042_: *mut crate::leanh::LeanObject,
    mut v_x_2043_: *mut crate::leanh::LeanObject,
    mut v_inst_2044_: *mut crate::leanh::LeanObject,
    mut v_inst_2045_: *mut crate::leanh::LeanObject,
    mut v_m_2046_: *mut crate::leanh::LeanObject,
    mut v_a_2047_: *mut crate::leanh::LeanObject,
    mut v_h_2048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_2042_, v_x_2043_, v_m_2046_, v_a_2047_,
    );
    return v___x_2049_;
}
pub unsafe fn l_Std_ExtHashMap_getKey___boxed(
    mut v_00_u03b1_2050_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2051_: *mut crate::leanh::LeanObject,
    mut v_x_2052_: *mut crate::leanh::LeanObject,
    mut v_x_2053_: *mut crate::leanh::LeanObject,
    mut v_inst_2054_: *mut crate::leanh::LeanObject,
    mut v_inst_2055_: *mut crate::leanh::LeanObject,
    mut v_m_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_h_2058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_Std_ExtHashMap_getKey(
        v_00_u03b1_2050_,
        v_00_u03b2_2051_,
        v_x_2052_,
        v_x_2053_,
        v_inst_2054_,
        v_inst_2055_,
        v_m_2056_,
        v_a_2057_,
        v_h_2058_,
    );
    crate::leanh::lean_dec(v_m_2056_);
    return v_res_2059_;
}
pub unsafe fn l_Std_ExtHashMap_getKeyD___redArg(
    mut v_x_2060_: *mut crate::leanh::LeanObject,
    mut v_x_2061_: *mut crate::leanh::LeanObject,
    mut v_m_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_fallback_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_2060_,
        v_x_2061_,
        v_m_2062_,
        v_a_2063_,
        v_fallback_2064_,
    );
    return v___x_2065_;
}
pub unsafe fn l_Std_ExtHashMap_getKeyD___redArg___boxed(
    mut v_x_2066_: *mut crate::leanh::LeanObject,
    mut v_x_2067_: *mut crate::leanh::LeanObject,
    mut v_m_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
    mut v_fallback_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2071_ = l_Std_ExtHashMap_getKeyD___redArg(
        v_x_2066_,
        v_x_2067_,
        v_m_2068_,
        v_a_2069_,
        v_fallback_2070_,
    );
    crate::leanh::lean_dec(v_fallback_2070_);
    crate::leanh::lean_dec(v_m_2068_);
    return v_res_2071_;
}
pub unsafe fn l_Std_ExtHashMap_getKeyD(
    mut v_00_u03b1_2072_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2073_: *mut crate::leanh::LeanObject,
    mut v_x_2074_: *mut crate::leanh::LeanObject,
    mut v_x_2075_: *mut crate::leanh::LeanObject,
    mut v_inst_2076_: *mut crate::leanh::LeanObject,
    mut v_inst_2077_: *mut crate::leanh::LeanObject,
    mut v_m_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_fallback_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2081_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_2074_,
        v_x_2075_,
        v_m_2078_,
        v_a_2079_,
        v_fallback_2080_,
    );
    return v___x_2081_;
}
pub unsafe fn l_Std_ExtHashMap_getKeyD___boxed(
    mut v_00_u03b1_2082_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2083_: *mut crate::leanh::LeanObject,
    mut v_x_2084_: *mut crate::leanh::LeanObject,
    mut v_x_2085_: *mut crate::leanh::LeanObject,
    mut v_inst_2086_: *mut crate::leanh::LeanObject,
    mut v_inst_2087_: *mut crate::leanh::LeanObject,
    mut v_m_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
    mut v_fallback_2090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2091_ = l_Std_ExtHashMap_getKeyD(
        v_00_u03b1_2082_,
        v_00_u03b2_2083_,
        v_x_2084_,
        v_x_2085_,
        v_inst_2086_,
        v_inst_2087_,
        v_m_2088_,
        v_a_2089_,
        v_fallback_2090_,
    );
    crate::leanh::lean_dec(v_fallback_2090_);
    crate::leanh::lean_dec(v_m_2088_);
    return v_res_2091_;
}
pub unsafe fn l_Std_ExtHashMap_getKey_x21___redArg(
    mut v_x_2092_: *mut crate::leanh::LeanObject,
    mut v_x_2093_: *mut crate::leanh::LeanObject,
    mut v_inst_2094_: *mut crate::leanh::LeanObject,
    mut v_m_2095_: *mut crate::leanh::LeanObject,
    mut v_a_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_2092_,
        v_x_2093_,
        v_inst_2094_,
        v_m_2095_,
        v_a_2096_,
    );
    return v___x_2097_;
}
pub unsafe fn l_Std_ExtHashMap_getKey_x21___redArg___boxed(
    mut v_x_2098_: *mut crate::leanh::LeanObject,
    mut v_x_2099_: *mut crate::leanh::LeanObject,
    mut v_inst_2100_: *mut crate::leanh::LeanObject,
    mut v_m_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2103_ = l_Std_ExtHashMap_getKey_x21___redArg(
        v_x_2098_,
        v_x_2099_,
        v_inst_2100_,
        v_m_2101_,
        v_a_2102_,
    );
    crate::leanh::lean_dec(v_m_2101_);
    crate::leanh::lean_dec(v_inst_2100_);
    return v_res_2103_;
}
pub unsafe fn l_Std_ExtHashMap_getKey_x21(
    mut v_00_u03b1_2104_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2105_: *mut crate::leanh::LeanObject,
    mut v_x_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
    mut v_inst_2108_: *mut crate::leanh::LeanObject,
    mut v_inst_2109_: *mut crate::leanh::LeanObject,
    mut v_inst_2110_: *mut crate::leanh::LeanObject,
    mut v_m_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2113_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_2106_,
        v_x_2107_,
        v_inst_2110_,
        v_m_2111_,
        v_a_2112_,
    );
    return v___x_2113_;
}
pub unsafe fn l_Std_ExtHashMap_getKey_x21___boxed(
    mut v_00_u03b1_2114_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2115_: *mut crate::leanh::LeanObject,
    mut v_x_2116_: *mut crate::leanh::LeanObject,
    mut v_x_2117_: *mut crate::leanh::LeanObject,
    mut v_inst_2118_: *mut crate::leanh::LeanObject,
    mut v_inst_2119_: *mut crate::leanh::LeanObject,
    mut v_inst_2120_: *mut crate::leanh::LeanObject,
    mut v_m_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2123_ = l_Std_ExtHashMap_getKey_x21(
        v_00_u03b1_2114_,
        v_00_u03b2_2115_,
        v_x_2116_,
        v_x_2117_,
        v_inst_2118_,
        v_inst_2119_,
        v_inst_2120_,
        v_m_2121_,
        v_a_2122_,
    );
    crate::leanh::lean_dec(v_m_2121_);
    crate::leanh::lean_dec(v_inst_2120_);
    return v_res_2123_;
}
pub unsafe fn l_Std_ExtHashMap_erase___redArg(
    mut v_x_2124_: *mut crate::leanh::LeanObject,
    mut v_x_2125_: *mut crate::leanh::LeanObject,
    mut v_m_2126_: *mut crate::leanh::LeanObject,
    mut v_a_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_2124_, v_x_2125_, v_m_2126_, v_a_2127_,
    );
    return v___x_2128_;
}
pub unsafe fn l_Std_ExtHashMap_erase(
    mut v_00_u03b1_2129_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2130_: *mut crate::leanh::LeanObject,
    mut v_x_2131_: *mut crate::leanh::LeanObject,
    mut v_x_2132_: *mut crate::leanh::LeanObject,
    mut v_inst_2133_: *mut crate::leanh::LeanObject,
    mut v_inst_2134_: *mut crate::leanh::LeanObject,
    mut v_m_2135_: *mut crate::leanh::LeanObject,
    mut v_a_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_2131_, v_x_2132_, v_m_2135_, v_a_2136_,
    );
    return v___x_2137_;
}
pub unsafe fn l_Std_ExtHashMap_size___redArg(
    mut v_m_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_2139_ = crate::leanh::lean_ctor_get(v_m_2138_, 0);
    crate::leanh::lean_inc(v_size_2139_);
    return v_size_2139_;
}
pub unsafe fn l_Std_ExtHashMap_size___redArg___boxed(
    mut v_m_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Std_ExtHashMap_size___redArg(v_m_2140_);
    crate::leanh::lean_dec(v_m_2140_);
    return v_res_2141_;
}
pub unsafe fn l_Std_ExtHashMap_size(
    mut v_00_u03b1_2142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2143_: *mut crate::leanh::LeanObject,
    mut v_x_2144_: *mut crate::leanh::LeanObject,
    mut v_x_2145_: *mut crate::leanh::LeanObject,
    mut v_inst_2146_: *mut crate::leanh::LeanObject,
    mut v_inst_2147_: *mut crate::leanh::LeanObject,
    mut v_m_2148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_2149_ = crate::leanh::lean_ctor_get(v_m_2148_, 0);
    crate::leanh::lean_inc(v_size_2149_);
    return v_size_2149_;
}
pub unsafe fn l_Std_ExtHashMap_size___boxed(
    mut v_00_u03b1_2150_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2151_: *mut crate::leanh::LeanObject,
    mut v_x_2152_: *mut crate::leanh::LeanObject,
    mut v_x_2153_: *mut crate::leanh::LeanObject,
    mut v_inst_2154_: *mut crate::leanh::LeanObject,
    mut v_inst_2155_: *mut crate::leanh::LeanObject,
    mut v_m_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Std_ExtHashMap_size(
        v_00_u03b1_2150_,
        v_00_u03b2_2151_,
        v_x_2152_,
        v_x_2153_,
        v_inst_2154_,
        v_inst_2155_,
        v_m_2156_,
    );
    crate::leanh::lean_dec(v_m_2156_);
    crate::leanh::lean_dec_ref(v_x_2153_);
    crate::leanh::lean_dec_ref(v_x_2152_);
    return v_res_2157_;
}
pub unsafe fn l_Std_ExtHashMap_isEmpty___redArg(
    mut v_m_2158_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: u8 = 0;
    v_size_2159_ = crate::leanh::lean_ctor_get(v_m_2158_, 0);
    v___x_2160_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2161_ = lean_nat_dec_eq(v_size_2159_, v___x_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Std_ExtHashMap_isEmpty___redArg___boxed(
    mut v_m_2162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2163_: u8 = 0;
    let mut v_r_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2163_ = l_Std_ExtHashMap_isEmpty___redArg(v_m_2162_);
    crate::leanh::lean_dec(v_m_2162_);
    v_r_2164_ = crate::leanh::lean_box((v_res_2163_) as usize);
    return v_r_2164_;
}
pub unsafe fn l_Std_ExtHashMap_isEmpty(
    mut v_00_u03b1_2165_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2166_: *mut crate::leanh::LeanObject,
    mut v_x_2167_: *mut crate::leanh::LeanObject,
    mut v_x_2168_: *mut crate::leanh::LeanObject,
    mut v_inst_2169_: *mut crate::leanh::LeanObject,
    mut v_inst_2170_: *mut crate::leanh::LeanObject,
    mut v_m_2171_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: u8 = 0;
    v_size_2172_ = crate::leanh::lean_ctor_get(v_m_2171_, 0);
    v___x_2173_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2174_ = lean_nat_dec_eq(v_size_2172_, v___x_2173_);
    return v___x_2174_;
}
pub unsafe fn l_Std_ExtHashMap_isEmpty___boxed(
    mut v_00_u03b1_2175_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2176_: *mut crate::leanh::LeanObject,
    mut v_x_2177_: *mut crate::leanh::LeanObject,
    mut v_x_2178_: *mut crate::leanh::LeanObject,
    mut v_inst_2179_: *mut crate::leanh::LeanObject,
    mut v_inst_2180_: *mut crate::leanh::LeanObject,
    mut v_m_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2182_: u8 = 0;
    let mut v_r_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2182_ = l_Std_ExtHashMap_isEmpty(
        v_00_u03b1_2175_,
        v_00_u03b2_2176_,
        v_x_2177_,
        v_x_2178_,
        v_inst_2179_,
        v_inst_2180_,
        v_m_2181_,
    );
    crate::leanh::lean_dec(v_m_2181_);
    crate::leanh::lean_dec_ref(v_x_2178_);
    crate::leanh::lean_dec_ref(v_x_2177_);
    v_r_2183_ = crate::leanh::lean_box((v_res_2182_) as usize);
    return v_r_2183_;
}
pub unsafe fn l_Std_ExtHashMap_ofList___redArg(
    mut v_inst_2207_: *mut crate::leanh::LeanObject,
    mut v_inst_2208_: *mut crate::leanh::LeanObject,
    mut v_l_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2210_ = l_Std_ExtHashMap_ofList___redArg___closed__11;
    v___x_2211_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_2210_,
        v_inst_2207_,
        v_inst_2208_,
        v___x_2211_,
        v_l_2209_,
    );
    return v___x_2212_;
}
pub unsafe fn l_Std_ExtHashMap_ofList(
    mut v_00_u03b1_2213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2214_: *mut crate::leanh::LeanObject,
    mut v_inst_2215_: *mut crate::leanh::LeanObject,
    mut v_inst_2216_: *mut crate::leanh::LeanObject,
    mut v_l_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2218_ = l_Std_ExtHashMap_ofList___redArg___closed__11;
    v___x_2219_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    v___x_2220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_2218_,
        v_inst_2215_,
        v_inst_2216_,
        v___x_2219_,
        v_l_2217_,
    );
    return v___x_2220_;
}
pub unsafe fn l_Std_ExtHashMap_unitOfList___redArg(
    mut v_inst_2221_: *mut crate::leanh::LeanObject,
    mut v_inst_2222_: *mut crate::leanh::LeanObject,
    mut v_l_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2224_ = l_Std_ExtHashMap_ofList___redArg___closed__11;
    v___x_2225_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    v___x_2226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_2224_,
        v_inst_2221_,
        v_inst_2222_,
        v___x_2225_,
        v_l_2223_,
    );
    return v___x_2226_;
}
pub unsafe fn l_Std_ExtHashMap_unitOfList(
    mut v_00_u03b1_2227_: *mut crate::leanh::LeanObject,
    mut v_inst_2228_: *mut crate::leanh::LeanObject,
    mut v_inst_2229_: *mut crate::leanh::LeanObject,
    mut v_l_2230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2231_ = l_Std_ExtHashMap_ofList___redArg___closed__11;
    v___x_2232_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    v___x_2233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_2231_,
        v_inst_2228_,
        v_inst_2229_,
        v___x_2232_,
        v_l_2230_,
    );
    return v___x_2233_;
}
pub unsafe fn l_Std_ExtHashMap_filter___redArg(
    mut v_f_2234_: *mut crate::leanh::LeanObject,
    mut v_m_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2234_, v_m_2235_);
    return v___x_2236_;
}
pub unsafe fn l_Std_ExtHashMap_filter(
    mut v_00_u03b1_2237_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2238_: *mut crate::leanh::LeanObject,
    mut v_x_2239_: *mut crate::leanh::LeanObject,
    mut v_x_2240_: *mut crate::leanh::LeanObject,
    mut v_inst_2241_: *mut crate::leanh::LeanObject,
    mut v_inst_2242_: *mut crate::leanh::LeanObject,
    mut v_f_2243_: *mut crate::leanh::LeanObject,
    mut v_m_2244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2243_, v_m_2244_);
    return v___x_2245_;
}
pub unsafe fn l_Std_ExtHashMap_filter___boxed(
    mut v_00_u03b1_2246_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2247_: *mut crate::leanh::LeanObject,
    mut v_x_2248_: *mut crate::leanh::LeanObject,
    mut v_x_2249_: *mut crate::leanh::LeanObject,
    mut v_inst_2250_: *mut crate::leanh::LeanObject,
    mut v_inst_2251_: *mut crate::leanh::LeanObject,
    mut v_f_2252_: *mut crate::leanh::LeanObject,
    mut v_m_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2254_ = l_Std_ExtHashMap_filter(
        v_00_u03b1_2246_,
        v_00_u03b2_2247_,
        v_x_2248_,
        v_x_2249_,
        v_inst_2250_,
        v_inst_2251_,
        v_f_2252_,
        v_m_2253_,
    );
    crate::leanh::lean_dec_ref(v_x_2249_);
    crate::leanh::lean_dec_ref(v_x_2248_);
    return v_res_2254_;
}
pub unsafe fn l_Std_ExtHashMap_map___redArg(
    mut v_f_2255_: *mut crate::leanh::LeanObject,
    mut v_m_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2257_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2255_, v_m_2256_);
    return v___x_2257_;
}
pub unsafe fn l_Std_ExtHashMap_map(
    mut v_00_u03b1_2258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2260_: *mut crate::leanh::LeanObject,
    mut v_x_2261_: *mut crate::leanh::LeanObject,
    mut v_x_2262_: *mut crate::leanh::LeanObject,
    mut v_inst_2263_: *mut crate::leanh::LeanObject,
    mut v_inst_2264_: *mut crate::leanh::LeanObject,
    mut v_f_2265_: *mut crate::leanh::LeanObject,
    mut v_m_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2265_, v_m_2266_);
    return v___x_2267_;
}
pub unsafe fn l_Std_ExtHashMap_map___boxed(
    mut v_00_u03b1_2268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2270_: *mut crate::leanh::LeanObject,
    mut v_x_2271_: *mut crate::leanh::LeanObject,
    mut v_x_2272_: *mut crate::leanh::LeanObject,
    mut v_inst_2273_: *mut crate::leanh::LeanObject,
    mut v_inst_2274_: *mut crate::leanh::LeanObject,
    mut v_f_2275_: *mut crate::leanh::LeanObject,
    mut v_m_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Std_ExtHashMap_map(
        v_00_u03b1_2268_,
        v_00_u03b2_2269_,
        v_00_u03b3_2270_,
        v_x_2271_,
        v_x_2272_,
        v_inst_2273_,
        v_inst_2274_,
        v_f_2275_,
        v_m_2276_,
    );
    crate::leanh::lean_dec_ref(v_x_2272_);
    crate::leanh::lean_dec_ref(v_x_2271_);
    return v_res_2277_;
}
pub unsafe fn l_Std_ExtHashMap_filterMap___redArg(
    mut v_f_2278_: *mut crate::leanh::LeanObject,
    mut v_m_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2278_, v_m_2279_);
    return v___x_2280_;
}
pub unsafe fn l_Std_ExtHashMap_filterMap(
    mut v_00_u03b1_2281_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2282_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2283_: *mut crate::leanh::LeanObject,
    mut v_x_2284_: *mut crate::leanh::LeanObject,
    mut v_x_2285_: *mut crate::leanh::LeanObject,
    mut v_inst_2286_: *mut crate::leanh::LeanObject,
    mut v_inst_2287_: *mut crate::leanh::LeanObject,
    mut v_f_2288_: *mut crate::leanh::LeanObject,
    mut v_m_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2290_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2288_, v_m_2289_);
    return v___x_2290_;
}
pub unsafe fn l_Std_ExtHashMap_filterMap___boxed(
    mut v_00_u03b1_2291_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2293_: *mut crate::leanh::LeanObject,
    mut v_x_2294_: *mut crate::leanh::LeanObject,
    mut v_x_2295_: *mut crate::leanh::LeanObject,
    mut v_inst_2296_: *mut crate::leanh::LeanObject,
    mut v_inst_2297_: *mut crate::leanh::LeanObject,
    mut v_f_2298_: *mut crate::leanh::LeanObject,
    mut v_m_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2300_ = l_Std_ExtHashMap_filterMap(
        v_00_u03b1_2291_,
        v_00_u03b2_2292_,
        v_00_u03b3_2293_,
        v_x_2294_,
        v_x_2295_,
        v_inst_2296_,
        v_inst_2297_,
        v_f_2298_,
        v_m_2299_,
    );
    crate::leanh::lean_dec_ref(v_x_2295_);
    crate::leanh::lean_dec_ref(v_x_2294_);
    return v_res_2300_;
}
pub unsafe fn l_Std_ExtHashMap_modify___redArg(
    mut v_x_2301_: *mut crate::leanh::LeanObject,
    mut v_x_2302_: *mut crate::leanh::LeanObject,
    mut v_m_2303_: *mut crate::leanh::LeanObject,
    mut v_a_2304_: *mut crate::leanh::LeanObject,
    mut v_f_2305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_2301_, v_x_2302_, v_m_2303_, v_a_2304_, v_f_2305_,
    );
    return v___x_2306_;
}
pub unsafe fn l_Std_ExtHashMap_modify(
    mut v_00_u03b1_2307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2308_: *mut crate::leanh::LeanObject,
    mut v_x_2309_: *mut crate::leanh::LeanObject,
    mut v_x_2310_: *mut crate::leanh::LeanObject,
    mut v_inst_2311_: *mut crate::leanh::LeanObject,
    mut v_inst_2312_: *mut crate::leanh::LeanObject,
    mut v_m_2313_: *mut crate::leanh::LeanObject,
    mut v_a_2314_: *mut crate::leanh::LeanObject,
    mut v_f_2315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_2309_, v_x_2310_, v_m_2313_, v_a_2314_, v_f_2315_,
    );
    return v___x_2316_;
}
pub unsafe fn l_Std_ExtHashMap_alter___redArg(
    mut v_x_2317_: *mut crate::leanh::LeanObject,
    mut v_x_2318_: *mut crate::leanh::LeanObject,
    mut v_m_2319_: *mut crate::leanh::LeanObject,
    mut v_a_2320_: *mut crate::leanh::LeanObject,
    mut v_f_2321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_2317_, v_x_2318_, v_m_2319_, v_a_2320_, v_f_2321_,
    );
    return v___x_2322_;
}
pub unsafe fn l_Std_ExtHashMap_alter(
    mut v_00_u03b1_2323_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2324_: *mut crate::leanh::LeanObject,
    mut v_x_2325_: *mut crate::leanh::LeanObject,
    mut v_x_2326_: *mut crate::leanh::LeanObject,
    mut v_inst_2327_: *mut crate::leanh::LeanObject,
    mut v_inst_2328_: *mut crate::leanh::LeanObject,
    mut v_m_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
    mut v_f_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_2325_, v_x_2326_, v_m_2329_, v_a_2330_, v_f_2331_,
    );
    return v___x_2332_;
}
pub unsafe fn l_Std_ExtHashMap_insertMany___redArg___lam__0(
    mut v_x_2333_: *mut crate::leanh::LeanObject,
    mut v_x_2334_: *mut crate::leanh::LeanObject,
    mut v_x_2335_: *mut crate::leanh::LeanObject,
    mut v_____s_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2337_ = crate::leanh::lean_ctor_get(v_x_2335_, 0);
    crate::leanh::lean_inc(v_fst_2337_);
    v_snd_2338_ = crate::leanh::lean_ctor_get(v_x_2335_, 1);
    crate::leanh::lean_inc(v_snd_2338_);
    crate::leanh::lean_dec_ref(v_x_2335_);
    v_m_2339_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2333_,
        v_x_2334_,
        v_____s_2336_,
        v_fst_2337_,
        v_snd_2338_,
    );
    v___x_2340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2340_, 0, v_m_2339_);
    return v___x_2340_;
}
pub unsafe fn l_Std_ExtHashMap_insertMany___redArg(
    mut v_x_2341_: *mut crate::leanh::LeanObject,
    mut v_x_2342_: *mut crate::leanh::LeanObject,
    mut v_inst_2343_: *mut crate::leanh::LeanObject,
    mut v_m_2344_: *mut crate::leanh::LeanObject,
    mut v_l_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2346_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2346_, 0, v_x_2341_);
    crate::leanh::lean_closure_set(v___f_2346_, 1, v_x_2342_);
    v___x_2347_ = crate::leanh::lean_apply_4(
        v_inst_2343_,
        crate::leanh::lean_box(0),
        v_l_2345_,
        v_m_2344_,
        v___f_2346_,
    );
    return v___x_2347_;
}
pub unsafe fn l_Std_ExtHashMap_insertMany(
    mut v_00_u03b1_2348_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2349_: *mut crate::leanh::LeanObject,
    mut v_x_2350_: *mut crate::leanh::LeanObject,
    mut v_x_2351_: *mut crate::leanh::LeanObject,
    mut v_inst_2352_: *mut crate::leanh::LeanObject,
    mut v_inst_2353_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_2354_: *mut crate::leanh::LeanObject,
    mut v_inst_2355_: *mut crate::leanh::LeanObject,
    mut v_m_2356_: *mut crate::leanh::LeanObject,
    mut v_l_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2358_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2358_, 0, v_x_2350_);
    crate::leanh::lean_closure_set(v___f_2358_, 1, v_x_2351_);
    v___x_2359_ = crate::leanh::lean_apply_4(
        v_inst_2355_,
        crate::leanh::lean_box(0),
        v_l_2357_,
        v_m_2356_,
        v___f_2358_,
    );
    return v___x_2359_;
}
pub unsafe fn l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0(
    mut v_x_2360_: *mut crate::leanh::LeanObject,
    mut v_x_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_____s_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = crate::leanh::lean_box(0);
    v_m_2365_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2360_,
        v_x_2361_,
        v_____s_2363_,
        v_a_2362_,
        v___x_2364_,
    );
    v___x_2366_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2366_, 0, v_m_2365_);
    return v___x_2366_;
}
pub unsafe fn l_Std_ExtHashMap_insertManyIfNewUnit___redArg(
    mut v_x_2367_: *mut crate::leanh::LeanObject,
    mut v_x_2368_: *mut crate::leanh::LeanObject,
    mut v_inst_2369_: *mut crate::leanh::LeanObject,
    mut v_m_2370_: *mut crate::leanh::LeanObject,
    mut v_l_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2372_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2372_, 0, v_x_2367_);
    crate::leanh::lean_closure_set(v___f_2372_, 1, v_x_2368_);
    v___x_2373_ = crate::leanh::lean_apply_4(
        v_inst_2369_,
        crate::leanh::lean_box(0),
        v_l_2371_,
        v_m_2370_,
        v___f_2372_,
    );
    return v___x_2373_;
}
pub unsafe fn l_Std_ExtHashMap_insertManyIfNewUnit(
    mut v_00_u03b1_2374_: *mut crate::leanh::LeanObject,
    mut v_x_2375_: *mut crate::leanh::LeanObject,
    mut v_x_2376_: *mut crate::leanh::LeanObject,
    mut v_inst_2377_: *mut crate::leanh::LeanObject,
    mut v_inst_2378_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_2379_: *mut crate::leanh::LeanObject,
    mut v_inst_2380_: *mut crate::leanh::LeanObject,
    mut v_m_2381_: *mut crate::leanh::LeanObject,
    mut v_l_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2383_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2383_, 0, v_x_2375_);
    crate::leanh::lean_closure_set(v___f_2383_, 1, v_x_2376_);
    v___x_2384_ = crate::leanh::lean_apply_4(
        v_inst_2380_,
        crate::leanh::lean_box(0),
        v_l_2382_,
        v_m_2381_,
        v___f_2383_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Std_ExtHashMap_union___redArg___lam__0(
    mut v_x_2385_: *mut crate::leanh::LeanObject,
    mut v_x_2386_: *mut crate::leanh::LeanObject,
    mut v_a_2387_: *mut crate::leanh::LeanObject,
    mut v_b_2388_: *mut crate::leanh::LeanObject,
    mut v_acc_2389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_2390_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2385_,
        v_x_2386_,
        v_acc_2389_,
        v_a_2387_,
        v_b_2388_,
    );
    v___x_2391_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2391_, 0, v_r_2390_);
    return v___x_2391_;
}
pub unsafe fn l_Std_ExtHashMap_union___redArg___lam__1(
    mut v___x_2392_: *mut crate::leanh::LeanObject,
    mut v___f_2393_: *mut crate::leanh::LeanObject,
    mut v_a_2394_: *mut crate::leanh::LeanObject,
    mut v_x_2395_: *mut crate::leanh::LeanObject,
    mut v___y_2396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_2392_, v___f_2393_, v_a_2394_, v___y_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_ExtHashMap_union___redArg(
    mut v_x_2400_: *mut crate::leanh::LeanObject,
    mut v_x_2401_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2402_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    v_size_2404_ = crate::leanh::lean_ctor_get(v_m_u2081_2402_, 0);
    v_buckets_2405_ = crate::leanh::lean_ctor_get(v_m_u2081_2402_, 1);
    v_size_2406_ = crate::leanh::lean_ctor_get(v_m_u2082_2403_, 0);
    v___x_2407_ = lean_nat_dec_le(v_size_2404_, v_size_2406_);
    if v___x_2407_ == 0 {
        let mut v___f_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2408_ = l_Std_ExtHashMap_union___redArg___closed__0;
        v___x_2409_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_2408_,
            v_x_2400_,
            v_x_2401_,
            v_m_u2081_2402_,
            v_m_u2082_2403_,
        );
        return v___x_2409_;
    } else {
        let mut v___f_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2413_: usize = 0;
        let mut v___x_2414_: usize = 0;
        let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_2405_);
        crate::leanh::lean_dec(v_m_u2081_2402_);
        v___f_2410_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2410_, 0, v_x_2400_);
        crate::leanh::lean_closure_set(v___f_2410_, 1, v_x_2401_);
        v___x_2411_ = l_Std_ExtHashMap_ofList___redArg___closed__9;
        v___f_2412_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2412_, 0, v___x_2411_);
        crate::leanh::lean_closure_set(v___f_2412_, 1, v___f_2410_);
        v_sz_2413_ = lean_array_size(v_buckets_2405_);
        v___x_2414_ = 0usize;
        v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2411_,
            v_buckets_2405_,
            v___f_2412_,
            v_sz_2413_,
            v___x_2414_,
            v_m_u2082_2403_,
        );
        return v___x_2415_;
    }
}
pub unsafe fn l_Std_ExtHashMap_union(
    mut v_00_u03b1_2416_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2417_: *mut crate::leanh::LeanObject,
    mut v_x_2418_: *mut crate::leanh::LeanObject,
    mut v_x_2419_: *mut crate::leanh::LeanObject,
    mut v_inst_2420_: *mut crate::leanh::LeanObject,
    mut v_inst_2421_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2422_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: u8 = 0;
    v_size_2424_ = crate::leanh::lean_ctor_get(v_m_u2081_2422_, 0);
    v_buckets_2425_ = crate::leanh::lean_ctor_get(v_m_u2081_2422_, 1);
    v_size_2426_ = crate::leanh::lean_ctor_get(v_m_u2082_2423_, 0);
    v___x_2427_ = lean_nat_dec_le(v_size_2424_, v_size_2426_);
    if v___x_2427_ == 0 {
        let mut v___f_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2428_ = l_Std_ExtHashMap_union___redArg___closed__0;
        v___x_2429_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_2428_,
            v_x_2418_,
            v_x_2419_,
            v_m_u2081_2422_,
            v_m_u2082_2423_,
        );
        return v___x_2429_;
    } else {
        let mut v___f_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2433_: usize = 0;
        let mut v___x_2434_: usize = 0;
        let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_2425_);
        crate::leanh::lean_dec(v_m_u2081_2422_);
        v___f_2430_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2430_, 0, v_x_2418_);
        crate::leanh::lean_closure_set(v___f_2430_, 1, v_x_2419_);
        v___x_2431_ = l_Std_ExtHashMap_ofList___redArg___closed__9;
        v___f_2432_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2432_, 0, v___x_2431_);
        crate::leanh::lean_closure_set(v___f_2432_, 1, v___f_2430_);
        v_sz_2433_ = lean_array_size(v_buckets_2425_);
        v___x_2434_ = 0usize;
        v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2431_,
            v_buckets_2425_,
            v___f_2432_,
            v_sz_2433_,
            v___x_2434_,
            v_m_u2082_2423_,
        );
        return v___x_2435_;
    }
}
pub unsafe fn l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_2436_: *mut crate::leanh::LeanObject,
    mut v_x_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2438_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashMap_union as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_2438_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2438_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2438_, 2, v_x_2436_);
    crate::leanh::lean_closure_set(v___x_2438_, 3, v_x_2437_);
    crate::leanh::lean_closure_set(v___x_2438_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2438_, 5, crate::leanh::lean_box(0));
    return v___x_2438_;
}
pub unsafe fn l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2439_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2440_: *mut crate::leanh::LeanObject,
    mut v_x_2441_: *mut crate::leanh::LeanObject,
    mut v_x_2442_: *mut crate::leanh::LeanObject,
    mut v_inst_2443_: *mut crate::leanh::LeanObject,
    mut v_inst_2444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2445_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashMap_union as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_2445_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2445_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2445_, 2, v_x_2441_);
    crate::leanh::lean_closure_set(v___x_2445_, 3, v_x_2442_);
    crate::leanh::lean_closure_set(v___x_2445_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2445_, 5, crate::leanh::lean_box(0));
    return v___x_2445_;
}
pub unsafe fn l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_2446_: *mut crate::leanh::LeanObject,
    mut v_x_2447_: *mut crate::leanh::LeanObject,
    mut v_inst_2448_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2449_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2450_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2451_: u8 = 0;
    v___x_2451_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_x_2446_,
        v_x_2447_,
        v_inst_2448_,
        v_m_u2081_2449_,
        v_m_u2082_2450_,
    );
    return v___x_2451_;
}
pub unsafe fn l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(
    mut v_x_2452_: *mut crate::leanh::LeanObject,
    mut v_x_2453_: *mut crate::leanh::LeanObject,
    mut v_inst_2454_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2455_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2457_: u8 = 0;
    let mut v_r_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2457_ = l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(
        v_x_2452_,
        v_x_2453_,
        v_inst_2454_,
        v_m_u2081_2455_,
        v_m_u2082_2456_,
    );
    v_r_2458_ = crate::leanh::lean_box((v_res_2457_) as usize);
    return v_r_2458_;
}
pub unsafe fn l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_2459_: *mut crate::leanh::LeanObject,
    mut v_x_2460_: *mut crate::leanh::LeanObject,
    mut v_inst_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2462_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2462_, 0, v_x_2459_);
    crate::leanh::lean_closure_set(v___f_2462_, 1, v_x_2460_);
    crate::leanh::lean_closure_set(v___f_2462_, 2, v_inst_2461_);
    return v___f_2462_;
}
pub unsafe fn l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2463_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2464_: *mut crate::leanh::LeanObject,
    mut v_x_2465_: *mut crate::leanh::LeanObject,
    mut v_x_2466_: *mut crate::leanh::LeanObject,
    mut v_inst_2467_: *mut crate::leanh::LeanObject,
    mut v_inst_2468_: *mut crate::leanh::LeanObject,
    mut v_inst_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2470_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2470_, 0, v_x_2465_);
    crate::leanh::lean_closure_set(v___f_2470_, 1, v_x_2466_);
    crate::leanh::lean_closure_set(v___f_2470_, 2, v_inst_2469_);
    return v___f_2470_;
}
pub unsafe fn l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(
    mut v_inst_2471_: *mut crate::leanh::LeanObject,
    mut v_inst_2472_: *mut crate::leanh::LeanObject,
    mut v_inst_2473_: *mut crate::leanh::LeanObject,
    mut v_x_2474_: *mut crate::leanh::LeanObject,
    mut v_x_2475_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2476_: u8 = 0;
    v___x_2476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_2471_,
        v_inst_2472_,
        v_inst_2473_,
        v_x_2474_,
        v_x_2475_,
    );
    return v___x_2476_;
}
pub unsafe fn l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(
    mut v_inst_2477_: *mut crate::leanh::LeanObject,
    mut v_inst_2478_: *mut crate::leanh::LeanObject,
    mut v_inst_2479_: *mut crate::leanh::LeanObject,
    mut v_x_2480_: *mut crate::leanh::LeanObject,
    mut v_x_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2482_: u8 = 0;
    let mut v_r_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2482_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(
        v_inst_2477_,
        v_inst_2478_,
        v_inst_2479_,
        v_x_2480_,
        v_x_2481_,
    );
    v_r_2483_ = crate::leanh::lean_box((v_res_2482_) as usize);
    return v_r_2483_;
}
pub unsafe fn l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(
    mut v_00_u03b1_2484_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2485_: *mut crate::leanh::LeanObject,
    mut v_inst_2486_: *mut crate::leanh::LeanObject,
    mut v_inst_2487_: *mut crate::leanh::LeanObject,
    mut v_inst_2488_: *mut crate::leanh::LeanObject,
    mut v_inst_2489_: *mut crate::leanh::LeanObject,
    mut v_inst_2490_: *mut crate::leanh::LeanObject,
    mut v_x_2491_: *mut crate::leanh::LeanObject,
    mut v_x_2492_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2493_: u8 = 0;
    v___x_2493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_2486_,
        v_inst_2488_,
        v_inst_2489_,
        v_x_2491_,
        v_x_2492_,
    );
    return v___x_2493_;
}
pub unsafe fn l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___boxed(
    mut v_00_u03b1_2494_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2495_: *mut crate::leanh::LeanObject,
    mut v_inst_2496_: *mut crate::leanh::LeanObject,
    mut v_inst_2497_: *mut crate::leanh::LeanObject,
    mut v_inst_2498_: *mut crate::leanh::LeanObject,
    mut v_inst_2499_: *mut crate::leanh::LeanObject,
    mut v_inst_2500_: *mut crate::leanh::LeanObject,
    mut v_x_2501_: *mut crate::leanh::LeanObject,
    mut v_x_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2503_: u8 = 0;
    let mut v_r_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2503_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(
        v_00_u03b1_2494_,
        v_00_u03b2_2495_,
        v_inst_2496_,
        v_inst_2497_,
        v_inst_2498_,
        v_inst_2499_,
        v_inst_2500_,
        v_x_2501_,
        v_x_2502_,
    );
    v_r_2504_ = crate::leanh::lean_box((v_res_2503_) as usize);
    return v_r_2504_;
}
pub unsafe fn l_Std_ExtHashMap_inter___redArg(
    mut v_x_2505_: *mut crate::leanh::LeanObject,
    mut v_x_2506_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2507_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2509_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_2505_,
        v_x_2506_,
        v_m_u2081_2507_,
        v_m_u2082_2508_,
    );
    return v___x_2509_;
}
pub unsafe fn l_Std_ExtHashMap_inter(
    mut v_00_u03b1_2510_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2511_: *mut crate::leanh::LeanObject,
    mut v_x_2512_: *mut crate::leanh::LeanObject,
    mut v_x_2513_: *mut crate::leanh::LeanObject,
    mut v_inst_2514_: *mut crate::leanh::LeanObject,
    mut v_inst_2515_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2516_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_2512_,
        v_x_2513_,
        v_m_u2081_2516_,
        v_m_u2082_2517_,
    );
    return v___x_2518_;
}
pub unsafe fn l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_2519_: *mut crate::leanh::LeanObject,
    mut v_x_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashMap_inter as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_2521_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2521_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2521_, 2, v_x_2519_);
    crate::leanh::lean_closure_set(v___x_2521_, 3, v_x_2520_);
    crate::leanh::lean_closure_set(v___x_2521_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2521_, 5, crate::leanh::lean_box(0));
    return v___x_2521_;
}
pub unsafe fn l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2522_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2523_: *mut crate::leanh::LeanObject,
    mut v_x_2524_: *mut crate::leanh::LeanObject,
    mut v_x_2525_: *mut crate::leanh::LeanObject,
    mut v_inst_2526_: *mut crate::leanh::LeanObject,
    mut v_inst_2527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2528_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashMap_inter as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_2528_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2528_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2528_, 2, v_x_2524_);
    crate::leanh::lean_closure_set(v___x_2528_, 3, v_x_2525_);
    crate::leanh::lean_closure_set(v___x_2528_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2528_, 5, crate::leanh::lean_box(0));
    return v___x_2528_;
}
pub unsafe fn l_Std_ExtHashMap_diff___redArg___lam__0(
    mut v_x_2529_: *mut crate::leanh::LeanObject,
    mut v_x_2530_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2531_: *mut crate::leanh::LeanObject,
    mut v___x_2532_: u8,
    mut v_k_2533_: *mut crate::leanh::LeanObject,
    mut v_x_2534_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2535_: u8 = 0;
    v___x_2535_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2529_,
        v_x_2530_,
        v_m_u2082_2531_,
        v_k_2533_,
    );
    if v___x_2535_ == 0 {
        return v___x_2532_;
    } else {
        let mut v___x_2536_: u8 = 0;
        v___x_2536_ = 0;
        return v___x_2536_;
    }
}
pub unsafe fn l_Std_ExtHashMap_diff___redArg___lam__0___boxed(
    mut v_x_2537_: *mut crate::leanh::LeanObject,
    mut v_x_2538_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2539_: *mut crate::leanh::LeanObject,
    mut v___x_2540_: *mut crate::leanh::LeanObject,
    mut v_k_2541_: *mut crate::leanh::LeanObject,
    mut v_x_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_106__boxed_2543_: u8 = 0;
    let mut v_res_2544_: u8 = 0;
    let mut v_r_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_106__boxed_2543_ = (crate::leanh::lean_unbox(v___x_2540_) as u8);
    v_res_2544_ = l_Std_ExtHashMap_diff___redArg___lam__0(
        v_x_2537_,
        v_x_2538_,
        v_m_u2082_2539_,
        v___x_106__boxed_2543_,
        v_k_2541_,
        v_x_2542_,
    );
    crate::leanh::lean_dec(v_x_2542_);
    crate::leanh::lean_dec(v_m_u2082_2539_);
    v_r_2545_ = crate::leanh::lean_box((v_res_2544_) as usize);
    return v_r_2545_;
}
pub unsafe fn l_Std_ExtHashMap_diff___redArg(
    mut v_x_2546_: *mut crate::leanh::LeanObject,
    mut v_x_2547_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2548_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    v_size_2550_ = crate::leanh::lean_ctor_get(v_m_u2081_2548_, 0);
    v_size_2551_ = crate::leanh::lean_ctor_get(v_m_u2082_2549_, 0);
    v___x_2552_ = lean_nat_dec_le(v_size_2550_, v_size_2551_);
    if v___x_2552_ == 0 {
        let mut v___f_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2553_ = l_Std_ExtHashMap_union___redArg___closed__0;
        v___x_2554_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_2553_,
            v_x_2546_,
            v_x_2547_,
            v_m_u2081_2548_,
            v_m_u2082_2549_,
        );
        return v___x_2554_;
    } else {
        let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2555_ = crate::leanh::lean_box((v___x_2552_) as usize);
        v___f_2556_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_2556_, 0, v_x_2546_);
        crate::leanh::lean_closure_set(v___f_2556_, 1, v_x_2547_);
        crate::leanh::lean_closure_set(v___f_2556_, 2, v_m_u2082_2549_);
        crate::leanh::lean_closure_set(v___f_2556_, 3, v___x_2555_);
        v___x_2557_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2556_, v_m_u2081_2548_);
        return v___x_2557_;
    }
}
pub unsafe fn l_Std_ExtHashMap_diff(
    mut v_00_u03b1_2558_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2559_: *mut crate::leanh::LeanObject,
    mut v_x_2560_: *mut crate::leanh::LeanObject,
    mut v_x_2561_: *mut crate::leanh::LeanObject,
    mut v_inst_2562_: *mut crate::leanh::LeanObject,
    mut v_inst_2563_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2564_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    v_size_2566_ = crate::leanh::lean_ctor_get(v_m_u2081_2564_, 0);
    v_size_2567_ = crate::leanh::lean_ctor_get(v_m_u2082_2565_, 0);
    v___x_2568_ = lean_nat_dec_le(v_size_2566_, v_size_2567_);
    if v___x_2568_ == 0 {
        let mut v___f_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2569_ = l_Std_ExtHashMap_union___redArg___closed__0;
        v___x_2570_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_2569_,
            v_x_2560_,
            v_x_2561_,
            v_m_u2081_2564_,
            v_m_u2082_2565_,
        );
        return v___x_2570_;
    } else {
        let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2571_ = crate::leanh::lean_box((v___x_2568_) as usize);
        v___f_2572_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_2572_, 0, v_x_2560_);
        crate::leanh::lean_closure_set(v___f_2572_, 1, v_x_2561_);
        crate::leanh::lean_closure_set(v___f_2572_, 2, v_m_u2082_2565_);
        crate::leanh::lean_closure_set(v___f_2572_, 3, v___x_2571_);
        v___x_2573_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2572_, v_m_u2081_2564_);
        return v___x_2573_;
    }
}
pub unsafe fn l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_2574_: *mut crate::leanh::LeanObject,
    mut v_x_2575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashMap_diff as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_2576_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2576_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2576_, 2, v_x_2574_);
    crate::leanh::lean_closure_set(v___x_2576_, 3, v_x_2575_);
    crate::leanh::lean_closure_set(v___x_2576_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2576_, 5, crate::leanh::lean_box(0));
    return v___x_2576_;
}
pub unsafe fn l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2577_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2578_: *mut crate::leanh::LeanObject,
    mut v_x_2579_: *mut crate::leanh::LeanObject,
    mut v_x_2580_: *mut crate::leanh::LeanObject,
    mut v_inst_2581_: *mut crate::leanh::LeanObject,
    mut v_inst_2582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2583_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashMap_diff as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_2583_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2583_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2583_, 2, v_x_2579_);
    crate::leanh::lean_closure_set(v___x_2583_, 3, v_x_2580_);
    crate::leanh::lean_closure_set(v___x_2583_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2583_, 5, crate::leanh::lean_box(0));
    return v___x_2583_;
}
pub unsafe fn l_Std_ExtHashMap_unitOfArray___redArg(
    mut v_inst_2588_: *mut crate::leanh::LeanObject,
    mut v_inst_2589_: *mut crate::leanh::LeanObject,
    mut v_l_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2591_ = l_Std_ExtHashMap_unitOfArray___redArg___closed__1;
    v___x_2592_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    v___x_2593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_2591_,
        v_inst_2588_,
        v_inst_2589_,
        v___x_2592_,
        v_l_2590_,
    );
    return v___x_2593_;
}
pub unsafe fn l_Std_ExtHashMap_unitOfArray(
    mut v_00_u03b1_2594_: *mut crate::leanh::LeanObject,
    mut v_inst_2595_: *mut crate::leanh::LeanObject,
    mut v_inst_2596_: *mut crate::leanh::LeanObject,
    mut v_l_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2598_ = l_Std_ExtHashMap_unitOfArray___redArg___closed__1;
    v___x_2599_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashMap_instEmptyCollection___closed__1,
    );
    v___x_2600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_2598_,
        v_inst_2595_,
        v_inst_2596_,
        v___x_2599_,
        v_l_2597_,
    );
    return v___x_2600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ExtHashMap_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_ExtDHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtHashMap_Basic(
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
pub unsafe fn initialize_Std_Data_ExtHashMap_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_ExtDHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_ExtHashMap_Basic(builtin);
}
