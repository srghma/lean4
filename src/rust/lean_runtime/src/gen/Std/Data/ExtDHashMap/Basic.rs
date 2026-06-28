// Lean compiler output
// Module: Std.Data.ExtDHashMap.Basic
// Imports: Std.Data.DHashMap.Lemmas Std.Data.DHashMap.Lemmas
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
    l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg,
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
    l_Std_DHashMap_Internal_Raw_u2080_alter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_beq___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_erase___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_expand___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_get___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_inter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_map___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_modify___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Lemmas::{
    initialize_Std_Data_DHashMap_Lemmas, runtime_initialize_Std_Data_DHashMap_Lemmas,
};
use crate::r#gen::Std::Data::DHashMap::RawDef::l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_div, lean_nat_mul,
};
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDHashMap_union___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDHashMap_union___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDHashMap_union___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDHashMap_union___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDHashMap_union___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDHashMap_union___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDHashMap_union___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDHashMap_union___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__10_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value:
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
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_ofList___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_ofList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtDHashMap_ofList___redArg___closed__1_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_ofList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_ExtDHashMap_mk___redArg(
    mut v_m_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_m_1655_);
    return v_m_1655_;
}
pub unsafe fn l_Std_ExtDHashMap_mk___redArg___boxed(
    mut v_m_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Std_ExtDHashMap_mk___redArg(v_m_1656_);
    crate::leanh::lean_dec_ref(v_m_1656_);
    return v_res_1657_;
}
pub unsafe fn l_Std_ExtDHashMap_mk(
    mut v_00_u03b1_1658_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1659_: *mut crate::leanh::LeanObject,
    mut v_x_1660_: *mut crate::leanh::LeanObject,
    mut v_x_1661_: *mut crate::leanh::LeanObject,
    mut v_m_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_m_1662_);
    return v_m_1662_;
}
pub unsafe fn l_Std_ExtDHashMap_mk___boxed(
    mut v_00_u03b1_1663_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1664_: *mut crate::leanh::LeanObject,
    mut v_x_1665_: *mut crate::leanh::LeanObject,
    mut v_x_1666_: *mut crate::leanh::LeanObject,
    mut v_m_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_ExtDHashMap_mk(
        v_00_u03b1_1663_,
        v_00_u03b2_1664_,
        v_x_1665_,
        v_x_1666_,
        v_m_1667_,
    );
    crate::leanh::lean_dec_ref(v_m_1667_);
    crate::leanh::lean_dec_ref(v_x_1666_);
    crate::leanh::lean_dec_ref(v_x_1665_);
    return v_res_1668_;
}
pub unsafe fn l_Std_ExtDHashMap_lift___redArg(
    mut v_f_1669_: *mut crate::leanh::LeanObject,
    mut v_m_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = crate::leanh::lean_apply_1(v_f_1669_, v_m_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Std_ExtDHashMap_lift(
    mut v_00_u03b1_1672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1673_: *mut crate::leanh::LeanObject,
    mut v_x_1674_: *mut crate::leanh::LeanObject,
    mut v_x_1675_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1676_: *mut crate::leanh::LeanObject,
    mut v_f_1677_: *mut crate::leanh::LeanObject,
    mut v_h_1678_: *mut crate::leanh::LeanObject,
    mut v_m_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = crate::leanh::lean_apply_1(v_f_1677_, v_m_1679_);
    return v___x_1680_;
}
pub unsafe fn l_Std_ExtDHashMap_lift___boxed(
    mut v_00_u03b1_1681_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1682_: *mut crate::leanh::LeanObject,
    mut v_x_1683_: *mut crate::leanh::LeanObject,
    mut v_x_1684_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1685_: *mut crate::leanh::LeanObject,
    mut v_f_1686_: *mut crate::leanh::LeanObject,
    mut v_h_1687_: *mut crate::leanh::LeanObject,
    mut v_m_1688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1689_ = l_Std_ExtDHashMap_lift(
        v_00_u03b1_1681_,
        v_00_u03b2_1682_,
        v_x_1683_,
        v_x_1684_,
        v_00_u03b3_1685_,
        v_f_1686_,
        v_h_1687_,
        v_m_1688_,
    );
    crate::leanh::lean_dec_ref(v_x_1684_);
    crate::leanh::lean_dec_ref(v_x_1683_);
    return v_res_1689_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082___redArg(
    mut v_f_1690_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1691_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1693_ = crate::leanh::lean_apply_2(v_f_1690_, v_m_u2081_1691_, v_m_u2082_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082(
    mut v_00_u03b1_1694_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1695_: *mut crate::leanh::LeanObject,
    mut v_x_1696_: *mut crate::leanh::LeanObject,
    mut v_x_1697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1698_: *mut crate::leanh::LeanObject,
    mut v_f_1699_: *mut crate::leanh::LeanObject,
    mut v_h_1700_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1701_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1703_ = crate::leanh::lean_apply_2(v_f_1699_, v_m_u2081_1701_, v_m_u2082_1702_);
    return v___x_1703_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082___boxed(
    mut v_00_u03b1_1704_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1705_: *mut crate::leanh::LeanObject,
    mut v_x_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1708_: *mut crate::leanh::LeanObject,
    mut v_f_1709_: *mut crate::leanh::LeanObject,
    mut v_h_1710_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1711_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Std_ExtDHashMap_lift_u2082(
        v_00_u03b1_1704_,
        v_00_u03b2_1705_,
        v_x_1706_,
        v_x_1707_,
        v_00_u03b3_1708_,
        v_f_1709_,
        v_h_1710_,
        v_m_u2081_1711_,
        v_m_u2082_1712_,
    );
    crate::leanh::lean_dec_ref(v_x_1707_);
    crate::leanh::lean_dec_ref(v_x_1706_);
    return v_res_1713_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn___redArg(
    mut v_m_1714_: *mut crate::leanh::LeanObject,
    mut v_f_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = crate::leanh::lean_apply_2(v_f_1715_, v_m_1714_, crate::leanh::lean_box(0));
    return v___x_1716_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn(
    mut v_00_u03b1_1717_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1718_: *mut crate::leanh::LeanObject,
    mut v_x_1719_: *mut crate::leanh::LeanObject,
    mut v_x_1720_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1721_: *mut crate::leanh::LeanObject,
    mut v_m_1722_: *mut crate::leanh::LeanObject,
    mut v_f_1723_: *mut crate::leanh::LeanObject,
    mut v_h_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = crate::leanh::lean_apply_2(v_f_1723_, v_m_1722_, crate::leanh::lean_box(0));
    return v___x_1725_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn___boxed(
    mut v_00_u03b1_1726_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1727_: *mut crate::leanh::LeanObject,
    mut v_x_1728_: *mut crate::leanh::LeanObject,
    mut v_x_1729_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1730_: *mut crate::leanh::LeanObject,
    mut v_m_1731_: *mut crate::leanh::LeanObject,
    mut v_f_1732_: *mut crate::leanh::LeanObject,
    mut v_h_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_ExtDHashMap_pliftOn(
        v_00_u03b1_1726_,
        v_00_u03b2_1727_,
        v_x_1728_,
        v_x_1729_,
        v_00_u03b3_1730_,
        v_m_1731_,
        v_f_1732_,
        v_h_1733_,
    );
    crate::leanh::lean_dec_ref(v_x_1729_);
    crate::leanh::lean_dec_ref(v_x_1728_);
    return v_res_1734_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___redArg(
    mut v_capacity_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1737_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1738_ = lean_nat_mul(v_capacity_1735_, v___x_1737_);
    v___x_1739_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1740_ = lean_nat_div(v___x_1738_, v___x_1739_);
    crate::leanh::lean_dec(v___x_1738_);
    v___x_1741_ = l_Nat_nextPowerOfTwo(v___x_1740_);
    crate::leanh::lean_dec(v___x_1740_);
    v___x_1742_ = crate::leanh::lean_box(0);
    v___x_1743_ = lean_mk_array(v___x_1741_, v___x_1742_);
    v___x_1744_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1744_, 0, v___x_1736_);
    crate::leanh::lean_ctor_set(v___x_1744_, 1, v___x_1743_);
    return v___x_1744_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___redArg___boxed(
    mut v_capacity_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Std_ExtDHashMap_emptyWithCapacity___redArg(v_capacity_1745_);
    crate::leanh::lean_dec(v_capacity_1745_);
    return v_res_1746_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity(
    mut v_00_u03b1_1747_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1748_: *mut crate::leanh::LeanObject,
    mut v_inst_1749_: *mut crate::leanh::LeanObject,
    mut v_inst_1750_: *mut crate::leanh::LeanObject,
    mut v_capacity_1751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1752_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1753_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1754_ = lean_nat_mul(v_capacity_1751_, v___x_1753_);
    v___x_1755_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1756_ = lean_nat_div(v___x_1754_, v___x_1755_);
    crate::leanh::lean_dec(v___x_1754_);
    v___x_1757_ = l_Nat_nextPowerOfTwo(v___x_1756_);
    crate::leanh::lean_dec(v___x_1756_);
    v___x_1758_ = crate::leanh::lean_box(0);
    v___x_1759_ = lean_mk_array(v___x_1757_, v___x_1758_);
    v___x_1760_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1760_, 0, v___x_1752_);
    crate::leanh::lean_ctor_set(v___x_1760_, 1, v___x_1759_);
    return v___x_1760_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___boxed(
    mut v_00_u03b1_1761_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1762_: *mut crate::leanh::LeanObject,
    mut v_inst_1763_: *mut crate::leanh::LeanObject,
    mut v_inst_1764_: *mut crate::leanh::LeanObject,
    mut v_capacity_1765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Std_ExtDHashMap_emptyWithCapacity(
        v_00_u03b1_1761_,
        v_00_u03b2_1762_,
        v_inst_1763_,
        v_inst_1764_,
        v_capacity_1765_,
    );
    crate::leanh::lean_dec(v_capacity_1765_);
    crate::leanh::lean_dec_ref(v_inst_1764_);
    crate::leanh::lean_dec_ref(v_inst_1763_);
    return v_res_1766_;
}
pub unsafe fn _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ = crate::leanh::lean_box(0);
    v___x_1768_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1769_ = lean_mk_array(v___x_1768_, v___x_1767_);
    return v___x_1769_;
}
pub unsafe fn _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__0_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0,
    );
    v___x_1771_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1772_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    crate::leanh::lean_ctor_set(v___x_1772_, 1, v___x_1770_);
    return v___x_1772_;
}
pub unsafe fn l_Std_ExtDHashMap_instEmptyCollection(
    mut v_00_u03b1_1773_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1774_: *mut crate::leanh::LeanObject,
    mut v_inst_1775_: *mut crate::leanh::LeanObject,
    mut v_inst_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    return v___x_1777_;
}
pub unsafe fn l_Std_ExtDHashMap_instEmptyCollection___boxed(
    mut v_00_u03b1_1778_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1779_: *mut crate::leanh::LeanObject,
    mut v_inst_1780_: *mut crate::leanh::LeanObject,
    mut v_inst_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Std_ExtDHashMap_instEmptyCollection(
        v_00_u03b1_1778_,
        v_00_u03b2_1779_,
        v_inst_1780_,
        v_inst_1781_,
    );
    crate::leanh::lean_dec_ref(v_inst_1781_);
    crate::leanh::lean_dec_ref(v_inst_1780_);
    return v_res_1782_;
}
pub unsafe fn l_Std_ExtDHashMap_instInhabited(
    mut v_00_u03b1_1783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1784_: *mut crate::leanh::LeanObject,
    mut v_inst_1785_: *mut crate::leanh::LeanObject,
    mut v_inst_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    return v___x_1787_;
}
pub unsafe fn l_Std_ExtDHashMap_instInhabited___boxed(
    mut v_00_u03b1_1788_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1789_: *mut crate::leanh::LeanObject,
    mut v_inst_1790_: *mut crate::leanh::LeanObject,
    mut v_inst_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1792_ = l_Std_ExtDHashMap_instInhabited(
        v_00_u03b1_1788_,
        v_00_u03b2_1789_,
        v_inst_1790_,
        v_inst_1791_,
    );
    crate::leanh::lean_dec_ref(v_inst_1791_);
    crate::leanh::lean_dec_ref(v_inst_1790_);
    return v_res_1792_;
}
pub unsafe fn l_Std_ExtDHashMap_insert___redArg(
    mut v_x_1793_: *mut crate::leanh::LeanObject,
    mut v_x_1794_: *mut crate::leanh::LeanObject,
    mut v_m_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_b_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1793_, v_x_1794_, v_m_1795_, v_a_1796_, v_b_1797_,
    );
    return v___x_1798_;
}
pub unsafe fn l_Std_ExtDHashMap_insert(
    mut v_00_u03b1_1799_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1800_: *mut crate::leanh::LeanObject,
    mut v_x_1801_: *mut crate::leanh::LeanObject,
    mut v_x_1802_: *mut crate::leanh::LeanObject,
    mut v_inst_1803_: *mut crate::leanh::LeanObject,
    mut v_inst_1804_: *mut crate::leanh::LeanObject,
    mut v_m_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_b_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1808_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1801_, v_x_1802_, v_m_1805_, v_a_1806_, v_b_1807_,
    );
    return v___x_1808_;
}
pub unsafe fn l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1809_: *mut crate::leanh::LeanObject,
    mut v_x_1810_: *mut crate::leanh::LeanObject,
    mut v_x_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1812_ = crate::leanh::lean_ctor_get(v_x_1811_, 0);
    crate::leanh::lean_inc(v_fst_1812_);
    v_snd_1813_ = crate::leanh::lean_ctor_get(v_x_1811_, 1);
    crate::leanh::lean_inc(v_snd_1813_);
    crate::leanh::lean_dec_ref(v_x_1811_);
    v___x_1814_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_1815_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1809_,
        v_x_1810_,
        v___x_1814_,
        v_fst_1812_,
        v_snd_1813_,
    );
    return v___x_1815_;
}
pub unsafe fn l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_1816_: *mut crate::leanh::LeanObject,
    mut v_x_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1818_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1818_, 0, v_x_1816_);
    crate::leanh::lean_closure_set(v___f_1818_, 1, v_x_1817_);
    return v___f_1818_;
}
pub unsafe fn l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1819_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1820_: *mut crate::leanh::LeanObject,
    mut v_x_1821_: *mut crate::leanh::LeanObject,
    mut v_x_1822_: *mut crate::leanh::LeanObject,
    mut v_inst_1823_: *mut crate::leanh::LeanObject,
    mut v_inst_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1825_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1825_, 0, v_x_1821_);
    crate::leanh::lean_closure_set(v___f_1825_, 1, v_x_1822_);
    return v___f_1825_;
}
pub unsafe fn l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1826_: *mut crate::leanh::LeanObject,
    mut v_x_1827_: *mut crate::leanh::LeanObject,
    mut v_x_1828_: *mut crate::leanh::LeanObject,
    mut v_x_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1830_ = crate::leanh::lean_ctor_get(v_x_1828_, 0);
    crate::leanh::lean_inc(v_fst_1830_);
    v_snd_1831_ = crate::leanh::lean_ctor_get(v_x_1828_, 1);
    crate::leanh::lean_inc(v_snd_1831_);
    crate::leanh::lean_dec_ref(v_x_1828_);
    v___x_1832_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1826_,
        v_x_1827_,
        v_x_1829_,
        v_fst_1830_,
        v_snd_1831_,
    );
    return v___x_1832_;
}
pub unsafe fn l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_1833_: *mut crate::leanh::LeanObject,
    mut v_x_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1835_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1835_, 0, v_x_1833_);
    crate::leanh::lean_closure_set(v___f_1835_, 1, v_x_1834_);
    return v___f_1835_;
}
pub unsafe fn l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1836_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1837_: *mut crate::leanh::LeanObject,
    mut v_x_1838_: *mut crate::leanh::LeanObject,
    mut v_x_1839_: *mut crate::leanh::LeanObject,
    mut v_inst_1840_: *mut crate::leanh::LeanObject,
    mut v_inst_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1842_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1842_, 0, v_x_1838_);
    crate::leanh::lean_closure_set(v___f_1842_, 1, v_x_1839_);
    return v___f_1842_;
}
pub unsafe fn l_Std_ExtDHashMap_insertIfNew___redArg(
    mut v_x_1843_: *mut crate::leanh::LeanObject,
    mut v_x_1844_: *mut crate::leanh::LeanObject,
    mut v_m_1845_: *mut crate::leanh::LeanObject,
    mut v_a_1846_: *mut crate::leanh::LeanObject,
    mut v_b_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1843_, v_x_1844_, v_m_1845_, v_a_1846_, v_b_1847_,
    );
    return v___x_1848_;
}
pub unsafe fn l_Std_ExtDHashMap_insertIfNew(
    mut v_00_u03b1_1849_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1850_: *mut crate::leanh::LeanObject,
    mut v_x_1851_: *mut crate::leanh::LeanObject,
    mut v_x_1852_: *mut crate::leanh::LeanObject,
    mut v_inst_1853_: *mut crate::leanh::LeanObject,
    mut v_inst_1854_: *mut crate::leanh::LeanObject,
    mut v_m_1855_: *mut crate::leanh::LeanObject,
    mut v_a_1856_: *mut crate::leanh::LeanObject,
    mut v_b_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1851_, v_x_1852_, v_m_1855_, v_a_1856_, v_b_1857_,
    );
    return v___x_1858_;
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsert___redArg(
    mut v_x_1859_: *mut crate::leanh::LeanObject,
    mut v_x_1860_: *mut crate::leanh::LeanObject,
    mut v_m_1861_: *mut crate::leanh::LeanObject,
    mut v_a_1862_: *mut crate::leanh::LeanObject,
    mut v_b_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1868_: u8 = 0;
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: u64 = 0;
    let mut v___x_1873_: u64 = 0;
    let mut v___x_1874_: u64 = 0;
    let mut v_fold_1875_: u64 = 0;
    let mut v___x_1876_: u64 = 0;
    let mut v___x_1877_: u64 = 0;
    let mut v___x_1878_: u64 = 0;
    let mut v___x_1879_: usize = 0;
    let mut v___x_1880_: usize = 0;
    let mut v___x_1881_: usize = 0;
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: usize = 0;
    let mut v_bkt_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v_val_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1864_ = crate::leanh::lean_ctor_get(v_m_1861_, 0);
                v_buckets_1865_ = crate::leanh::lean_ctor_get(v_m_1861_, 1);
                v_isSharedCheck_1916_ = (!crate::leanh::lean_is_exclusive(v_m_1861_)) as u8;
                if v_isSharedCheck_1916_ == 0 {
                    v___x_1867_ = v_m_1861_;
                    v_isShared_1868_ = v_isSharedCheck_1916_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1865_);
                    crate::leanh::lean_inc(v_size_1864_);
                    crate::leanh::lean_dec(v_m_1861_);
                    v___x_1867_ = crate::leanh::lean_box(0);
                    v_isShared_1868_ = v_isSharedCheck_1916_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1869_ = lean_array_get_size(v_buckets_1865_);
                crate::leanh::lean_inc_ref(v_x_1860_);
                crate::leanh::lean_inc_n(v_a_1862_, 2);
                v___x_1870_ = crate::leanh::lean_apply_1(v_x_1860_, v_a_1862_);
                v___x_1871_ = 32u64;
                v___x_1872_ = crate::leanh::lean_unbox_uint64(v___x_1870_);
                v___x_1873_ = lean_uint64_shift_right(v___x_1872_, v___x_1871_);
                v___x_1874_ = crate::leanh::lean_unbox_uint64(v___x_1870_);
                crate::leanh::lean_dec_ref(v___x_1870_);
                v_fold_1875_ = lean_uint64_xor(v___x_1874_, v___x_1873_);
                v___x_1876_ = 16u64;
                v___x_1877_ = lean_uint64_shift_right(v_fold_1875_, v___x_1876_);
                v___x_1878_ = lean_uint64_xor(v_fold_1875_, v___x_1877_);
                v___x_1879_ = lean_uint64_to_usize(v___x_1878_);
                v___x_1880_ = lean_usize_of_nat(v___x_1869_);
                v___x_1881_ = 1usize;
                v___x_1882_ = lean_usize_sub(v___x_1880_, v___x_1881_);
                v___x_1883_ = lean_usize_land(v___x_1879_, v___x_1882_);
                v_bkt_1884_ = lean_array_uget_borrowed(v_buckets_1865_, v___x_1883_);
                crate::leanh::lean_inc(v_bkt_1884_);
                crate::leanh::lean_inc_ref(v_x_1859_);
                v___x_1885_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1859_,
                    v_a_1862_,
                    v_bkt_1884_,
                );
                if v___x_1885_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_1859_);
                    v___x_1886_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1887_ = lean_nat_add(v_size_1864_, v___x_1886_);
                    crate::leanh::lean_dec(v_size_1864_);
                    crate::leanh::lean_inc(v_bkt_1884_);
                    v___x_1888_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1888_, 0, v_a_1862_);
                    crate::leanh::lean_ctor_set(v___x_1888_, 1, v_b_1863_);
                    crate::leanh::lean_ctor_set(v___x_1888_, 2, v_bkt_1884_);
                    v_buckets_x27_1889_ =
                        lean_array_uset(v_buckets_1865_, v___x_1883_, v___x_1888_);
                    v___x_1890_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1891_ = lean_nat_mul(v_size_x27_1887_, v___x_1890_);
                    v___x_1892_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1893_ = lean_nat_div(v___x_1891_, v___x_1892_);
                    crate::leanh::lean_dec(v___x_1891_);
                    v___x_1894_ = lean_array_get_size(v_buckets_x27_1889_);
                    v___x_1895_ = lean_nat_dec_le(v___x_1893_, v___x_1894_);
                    crate::leanh::lean_dec(v___x_1893_);
                    if v___x_1895_ == 0 {
                        v_val_1896_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_1860_,
                            v_buckets_x27_1889_,
                        );
                        if v_isShared_1868_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1867_, 1, v_val_1896_);
                            crate::leanh::lean_ctor_set(v___x_1867_, 0, v_size_x27_1887_);
                            v___x_1898_ = v___x_1867_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1901_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1901_,
                                0,
                                v_size_x27_1887_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_val_1896_);
                            v___x_1898_ = v_reuseFailAlloc_1901_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1860_);
                        if v_isShared_1868_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1867_, 1, v_buckets_x27_1889_);
                            crate::leanh::lean_ctor_set(v___x_1867_, 0, v_size_x27_1887_);
                            v___x_1903_ = v___x_1867_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1906_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1906_,
                                0,
                                v_size_x27_1887_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1906_,
                                1,
                                v_buckets_x27_1889_,
                            );
                            v___x_1903_ = v_reuseFailAlloc_1906_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1884_);
                    crate::leanh::lean_dec_ref(v_x_1860_);
                    v___x_1907_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1908_ =
                        lean_array_uset(v_buckets_1865_, v___x_1883_, v___x_1907_);
                    v___x_1909_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_x_1859_,
                        v_a_1862_,
                        v_b_1863_,
                        v_bkt_1884_,
                    );
                    v___x_1910_ = lean_array_uset(v_buckets_x27_1908_, v___x_1883_, v___x_1909_);
                    if v_isShared_1868_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1867_, 1, v___x_1910_);
                        v___x_1912_ = v___x_1867_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1915_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_size_1864_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1910_);
                        v___x_1912_ = v_reuseFailAlloc_1915_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1899_ = crate::leanh::lean_box((v___x_1885_) as usize);
                v___x_1900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1899_);
                crate::leanh::lean_ctor_set(v___x_1900_, 1, v___x_1898_);
                return v___x_1900_;
            }
            3 => {
                v___x_1904_ = crate::leanh::lean_box((v___x_1885_) as usize);
                v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1903_);
                return v___x_1905_;
            }
            4 => {
                v___x_1913_ = crate::leanh::lean_box((v___x_1885_) as usize);
                v___x_1914_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1913_);
                crate::leanh::lean_ctor_set(v___x_1914_, 1, v___x_1912_);
                return v___x_1914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsert(
    mut v_00_u03b1_1917_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1918_: *mut crate::leanh::LeanObject,
    mut v_x_1919_: *mut crate::leanh::LeanObject,
    mut v_x_1920_: *mut crate::leanh::LeanObject,
    mut v_inst_1921_: *mut crate::leanh::LeanObject,
    mut v_inst_1922_: *mut crate::leanh::LeanObject,
    mut v_m_1923_: *mut crate::leanh::LeanObject,
    mut v_a_1924_: *mut crate::leanh::LeanObject,
    mut v_b_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u64 = 0;
    let mut v___x_1934_: u64 = 0;
    let mut v___x_1935_: u64 = 0;
    let mut v___x_1936_: u64 = 0;
    let mut v_fold_1937_: u64 = 0;
    let mut v___x_1938_: u64 = 0;
    let mut v___x_1939_: u64 = 0;
    let mut v___x_1940_: u64 = 0;
    let mut v___x_1941_: usize = 0;
    let mut v___x_1942_: usize = 0;
    let mut v___x_1943_: usize = 0;
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: usize = 0;
    let mut v_bkt_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: u8 = 0;
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v_val_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1926_ = crate::leanh::lean_ctor_get(v_m_1923_, 0);
                v_buckets_1927_ = crate::leanh::lean_ctor_get(v_m_1923_, 1);
                v_isSharedCheck_1978_ = (!crate::leanh::lean_is_exclusive(v_m_1923_)) as u8;
                if v_isSharedCheck_1978_ == 0 {
                    v___x_1929_ = v_m_1923_;
                    v_isShared_1930_ = v_isSharedCheck_1978_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1927_);
                    crate::leanh::lean_inc(v_size_1926_);
                    crate::leanh::lean_dec(v_m_1923_);
                    v___x_1929_ = crate::leanh::lean_box(0);
                    v_isShared_1930_ = v_isSharedCheck_1978_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1931_ = lean_array_get_size(v_buckets_1927_);
                crate::leanh::lean_inc_ref(v_x_1920_);
                crate::leanh::lean_inc_n(v_a_1924_, 2);
                v___x_1932_ = crate::leanh::lean_apply_1(v_x_1920_, v_a_1924_);
                v___x_1933_ = 32u64;
                v___x_1934_ = crate::leanh::lean_unbox_uint64(v___x_1932_);
                v___x_1935_ = lean_uint64_shift_right(v___x_1934_, v___x_1933_);
                v___x_1936_ = crate::leanh::lean_unbox_uint64(v___x_1932_);
                crate::leanh::lean_dec_ref(v___x_1932_);
                v_fold_1937_ = lean_uint64_xor(v___x_1936_, v___x_1935_);
                v___x_1938_ = 16u64;
                v___x_1939_ = lean_uint64_shift_right(v_fold_1937_, v___x_1938_);
                v___x_1940_ = lean_uint64_xor(v_fold_1937_, v___x_1939_);
                v___x_1941_ = lean_uint64_to_usize(v___x_1940_);
                v___x_1942_ = lean_usize_of_nat(v___x_1931_);
                v___x_1943_ = 1usize;
                v___x_1944_ = lean_usize_sub(v___x_1942_, v___x_1943_);
                v___x_1945_ = lean_usize_land(v___x_1941_, v___x_1944_);
                v_bkt_1946_ = lean_array_uget_borrowed(v_buckets_1927_, v___x_1945_);
                crate::leanh::lean_inc(v_bkt_1946_);
                crate::leanh::lean_inc_ref(v_x_1919_);
                v___x_1947_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1919_,
                    v_a_1924_,
                    v_bkt_1946_,
                );
                if v___x_1947_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_1919_);
                    v___x_1948_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1949_ = lean_nat_add(v_size_1926_, v___x_1948_);
                    crate::leanh::lean_dec(v_size_1926_);
                    crate::leanh::lean_inc(v_bkt_1946_);
                    v___x_1950_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1950_, 0, v_a_1924_);
                    crate::leanh::lean_ctor_set(v___x_1950_, 1, v_b_1925_);
                    crate::leanh::lean_ctor_set(v___x_1950_, 2, v_bkt_1946_);
                    v_buckets_x27_1951_ =
                        lean_array_uset(v_buckets_1927_, v___x_1945_, v___x_1950_);
                    v___x_1952_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1953_ = lean_nat_mul(v_size_x27_1949_, v___x_1952_);
                    v___x_1954_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1955_ = lean_nat_div(v___x_1953_, v___x_1954_);
                    crate::leanh::lean_dec(v___x_1953_);
                    v___x_1956_ = lean_array_get_size(v_buckets_x27_1951_);
                    v___x_1957_ = lean_nat_dec_le(v___x_1955_, v___x_1956_);
                    crate::leanh::lean_dec(v___x_1955_);
                    if v___x_1957_ == 0 {
                        v_val_1958_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_1920_,
                            v_buckets_x27_1951_,
                        );
                        if v_isShared_1930_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1929_, 1, v_val_1958_);
                            crate::leanh::lean_ctor_set(v___x_1929_, 0, v_size_x27_1949_);
                            v___x_1960_ = v___x_1929_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1963_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1963_,
                                0,
                                v_size_x27_1949_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_val_1958_);
                            v___x_1960_ = v_reuseFailAlloc_1963_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1920_);
                        if v_isShared_1930_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1929_, 1, v_buckets_x27_1951_);
                            crate::leanh::lean_ctor_set(v___x_1929_, 0, v_size_x27_1949_);
                            v___x_1965_ = v___x_1929_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1968_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1968_,
                                0,
                                v_size_x27_1949_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1968_,
                                1,
                                v_buckets_x27_1951_,
                            );
                            v___x_1965_ = v_reuseFailAlloc_1968_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1946_);
                    crate::leanh::lean_dec_ref(v_x_1920_);
                    v___x_1969_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1970_ =
                        lean_array_uset(v_buckets_1927_, v___x_1945_, v___x_1969_);
                    v___x_1971_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_x_1919_,
                        v_a_1924_,
                        v_b_1925_,
                        v_bkt_1946_,
                    );
                    v___x_1972_ = lean_array_uset(v_buckets_x27_1970_, v___x_1945_, v___x_1971_);
                    if v_isShared_1930_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1929_, 1, v___x_1972_);
                        v___x_1974_ = v___x_1929_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_size_1926_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1972_);
                        v___x_1974_ = v_reuseFailAlloc_1977_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1961_ = crate::leanh::lean_box((v___x_1947_) as usize);
                v___x_1962_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1961_);
                crate::leanh::lean_ctor_set(v___x_1962_, 1, v___x_1960_);
                return v___x_1962_;
            }
            3 => {
                v___x_1966_ = crate::leanh::lean_box((v___x_1947_) as usize);
                v___x_1967_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1967_, 0, v___x_1966_);
                crate::leanh::lean_ctor_set(v___x_1967_, 1, v___x_1965_);
                return v___x_1967_;
            }
            4 => {
                v___x_1975_ = crate::leanh::lean_box((v___x_1947_) as usize);
                v___x_1976_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1976_, 0, v___x_1975_);
                crate::leanh::lean_ctor_set(v___x_1976_, 1, v___x_1974_);
                return v___x_1976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsertIfNew___redArg(
    mut v_x_1979_: *mut crate::leanh::LeanObject,
    mut v_x_1980_: *mut crate::leanh::LeanObject,
    mut v_m_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_b_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u64 = 0;
    let mut v___x_1989_: u64 = 0;
    let mut v___x_1990_: u64 = 0;
    let mut v___x_1991_: u64 = 0;
    let mut v_fold_1992_: u64 = 0;
    let mut v___x_1993_: u64 = 0;
    let mut v___x_1994_: u64 = 0;
    let mut v___x_1995_: u64 = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: usize = 0;
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: usize = 0;
    let mut v___x_2000_: usize = 0;
    let mut v_bkt_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: u8 = 0;
    let mut v_val_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2027_: u8 = 0;
    let mut v_unused_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1984_ = crate::leanh::lean_ctor_get(v_m_1981_, 0);
                v_buckets_1985_ = crate::leanh::lean_ctor_get(v_m_1981_, 1);
                v___x_1986_ = lean_array_get_size(v_buckets_1985_);
                crate::leanh::lean_inc_ref(v_x_1980_);
                crate::leanh::lean_inc_n(v_a_1982_, 2);
                v___x_1987_ = crate::leanh::lean_apply_1(v_x_1980_, v_a_1982_);
                v___x_1988_ = 32u64;
                v___x_1989_ = crate::leanh::lean_unbox_uint64(v___x_1987_);
                v___x_1990_ = lean_uint64_shift_right(v___x_1989_, v___x_1988_);
                v___x_1991_ = crate::leanh::lean_unbox_uint64(v___x_1987_);
                crate::leanh::lean_dec_ref(v___x_1987_);
                v_fold_1992_ = lean_uint64_xor(v___x_1991_, v___x_1990_);
                v___x_1993_ = 16u64;
                v___x_1994_ = lean_uint64_shift_right(v_fold_1992_, v___x_1993_);
                v___x_1995_ = lean_uint64_xor(v_fold_1992_, v___x_1994_);
                v___x_1996_ = lean_uint64_to_usize(v___x_1995_);
                v___x_1997_ = lean_usize_of_nat(v___x_1986_);
                v___x_1998_ = 1usize;
                v___x_1999_ = lean_usize_sub(v___x_1997_, v___x_1998_);
                v___x_2000_ = lean_usize_land(v___x_1996_, v___x_1999_);
                v_bkt_2001_ = lean_array_uget_borrowed(v_buckets_1985_, v___x_2000_);
                crate::leanh::lean_inc(v_bkt_2001_);
                v___x_2002_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1979_,
                    v_a_1982_,
                    v_bkt_2001_,
                );
                if v___x_2002_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1985_);
                    crate::leanh::lean_inc(v_size_1984_);
                    v_isSharedCheck_2027_ = (!crate::leanh::lean_is_exclusive(v_m_1981_)) as u8;
                    if v_isSharedCheck_2027_ == 0 {
                        v_unused_2028_ = crate::leanh::lean_ctor_get(v_m_1981_, 1);
                        crate::leanh::lean_dec(v_unused_2028_);
                        v_unused_2029_ = crate::leanh::lean_ctor_get(v_m_1981_, 0);
                        crate::leanh::lean_dec(v_unused_2029_);
                        v___x_2004_ = v_m_1981_;
                        v_isShared_2005_ = v_isSharedCheck_2027_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1981_);
                        v___x_2004_ = crate::leanh::lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2027_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1983_);
                    crate::leanh::lean_dec(v_a_1982_);
                    crate::leanh::lean_dec_ref(v_x_1980_);
                    v___x_2030_ = crate::leanh::lean_box((v___x_2002_) as usize);
                    v___x_2031_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2031_, 0, v___x_2030_);
                    crate::leanh::lean_ctor_set(v___x_2031_, 1, v_m_1981_);
                    return v___x_2031_;
                }
            }
            1 => {
                v___x_2006_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2007_ = lean_nat_add(v_size_1984_, v___x_2006_);
                crate::leanh::lean_dec(v_size_1984_);
                crate::leanh::lean_inc(v_bkt_2001_);
                v___x_2008_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2008_, 0, v_a_1982_);
                crate::leanh::lean_ctor_set(v___x_2008_, 1, v_b_1983_);
                crate::leanh::lean_ctor_set(v___x_2008_, 2, v_bkt_2001_);
                v_buckets_x27_2009_ = lean_array_uset(v_buckets_1985_, v___x_2000_, v___x_2008_);
                v___x_2010_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2011_ = lean_nat_mul(v_size_x27_2007_, v___x_2010_);
                v___x_2012_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2013_ = lean_nat_div(v___x_2011_, v___x_2012_);
                crate::leanh::lean_dec(v___x_2011_);
                v___x_2014_ = lean_array_get_size(v_buckets_x27_2009_);
                v___x_2015_ = lean_nat_dec_le(v___x_2013_, v___x_2014_);
                crate::leanh::lean_dec(v___x_2013_);
                if v___x_2015_ == 0 {
                    v_val_2016_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1980_,
                        v_buckets_x27_2009_,
                    );
                    if v_isShared_2005_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2004_, 1, v_val_2016_);
                        crate::leanh::lean_ctor_set(v___x_2004_, 0, v_size_x27_2007_);
                        v___x_2018_ = v___x_2004_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_size_x27_2007_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_val_2016_);
                        v___x_2018_ = v_reuseFailAlloc_2021_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1980_);
                    if v_isShared_2005_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2004_, 1, v_buckets_x27_2009_);
                        crate::leanh::lean_ctor_set(v___x_2004_, 0, v_size_x27_2007_);
                        v___x_2023_ = v___x_2004_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2026_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_size_x27_2007_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_buckets_x27_2009_);
                        v___x_2023_ = v_reuseFailAlloc_2026_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2019_ = crate::leanh::lean_box((v___x_2002_) as usize);
                v___x_2020_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2020_, 0, v___x_2019_);
                crate::leanh::lean_ctor_set(v___x_2020_, 1, v___x_2018_);
                return v___x_2020_;
            }
            3 => {
                v___x_2024_ = crate::leanh::lean_box((v___x_2002_) as usize);
                v___x_2025_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2024_);
                crate::leanh::lean_ctor_set(v___x_2025_, 1, v___x_2023_);
                return v___x_2025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsertIfNew(
    mut v_00_u03b1_2032_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2033_: *mut crate::leanh::LeanObject,
    mut v_x_2034_: *mut crate::leanh::LeanObject,
    mut v_x_2035_: *mut crate::leanh::LeanObject,
    mut v_inst_2036_: *mut crate::leanh::LeanObject,
    mut v_inst_2037_: *mut crate::leanh::LeanObject,
    mut v_m_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_b_2040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u64 = 0;
    let mut v___x_2046_: u64 = 0;
    let mut v___x_2047_: u64 = 0;
    let mut v___x_2048_: u64 = 0;
    let mut v_fold_2049_: u64 = 0;
    let mut v___x_2050_: u64 = 0;
    let mut v___x_2051_: u64 = 0;
    let mut v___x_2052_: u64 = 0;
    let mut v___x_2053_: usize = 0;
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: usize = 0;
    let mut v___x_2056_: usize = 0;
    let mut v___x_2057_: usize = 0;
    let mut v_bkt_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v_val_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_unused_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2041_ = crate::leanh::lean_ctor_get(v_m_2038_, 0);
                v_buckets_2042_ = crate::leanh::lean_ctor_get(v_m_2038_, 1);
                v___x_2043_ = lean_array_get_size(v_buckets_2042_);
                crate::leanh::lean_inc_ref(v_x_2035_);
                crate::leanh::lean_inc_n(v_a_2039_, 2);
                v___x_2044_ = crate::leanh::lean_apply_1(v_x_2035_, v_a_2039_);
                v___x_2045_ = 32u64;
                v___x_2046_ = crate::leanh::lean_unbox_uint64(v___x_2044_);
                v___x_2047_ = lean_uint64_shift_right(v___x_2046_, v___x_2045_);
                v___x_2048_ = crate::leanh::lean_unbox_uint64(v___x_2044_);
                crate::leanh::lean_dec_ref(v___x_2044_);
                v_fold_2049_ = lean_uint64_xor(v___x_2048_, v___x_2047_);
                v___x_2050_ = 16u64;
                v___x_2051_ = lean_uint64_shift_right(v_fold_2049_, v___x_2050_);
                v___x_2052_ = lean_uint64_xor(v_fold_2049_, v___x_2051_);
                v___x_2053_ = lean_uint64_to_usize(v___x_2052_);
                v___x_2054_ = lean_usize_of_nat(v___x_2043_);
                v___x_2055_ = 1usize;
                v___x_2056_ = lean_usize_sub(v___x_2054_, v___x_2055_);
                v___x_2057_ = lean_usize_land(v___x_2053_, v___x_2056_);
                v_bkt_2058_ = lean_array_uget_borrowed(v_buckets_2042_, v___x_2057_);
                crate::leanh::lean_inc(v_bkt_2058_);
                v___x_2059_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_2034_,
                    v_a_2039_,
                    v_bkt_2058_,
                );
                if v___x_2059_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2042_);
                    crate::leanh::lean_inc(v_size_2041_);
                    v_isSharedCheck_2084_ = (!crate::leanh::lean_is_exclusive(v_m_2038_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v_unused_2085_ = crate::leanh::lean_ctor_get(v_m_2038_, 1);
                        crate::leanh::lean_dec(v_unused_2085_);
                        v_unused_2086_ = crate::leanh::lean_ctor_get(v_m_2038_, 0);
                        crate::leanh::lean_dec(v_unused_2086_);
                        v___x_2061_ = v_m_2038_;
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2038_);
                        v___x_2061_ = crate::leanh::lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2040_);
                    crate::leanh::lean_dec(v_a_2039_);
                    crate::leanh::lean_dec_ref(v_x_2035_);
                    v___x_2087_ = crate::leanh::lean_box((v___x_2059_) as usize);
                    v___x_2088_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 1, v_m_2038_);
                    return v___x_2088_;
                }
            }
            1 => {
                v___x_2063_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2064_ = lean_nat_add(v_size_2041_, v___x_2063_);
                crate::leanh::lean_dec(v_size_2041_);
                crate::leanh::lean_inc(v_bkt_2058_);
                v___x_2065_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2065_, 0, v_a_2039_);
                crate::leanh::lean_ctor_set(v___x_2065_, 1, v_b_2040_);
                crate::leanh::lean_ctor_set(v___x_2065_, 2, v_bkt_2058_);
                v_buckets_x27_2066_ = lean_array_uset(v_buckets_2042_, v___x_2057_, v___x_2065_);
                v___x_2067_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2068_ = lean_nat_mul(v_size_x27_2064_, v___x_2067_);
                v___x_2069_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2070_ = lean_nat_div(v___x_2068_, v___x_2069_);
                crate::leanh::lean_dec(v___x_2068_);
                v___x_2071_ = lean_array_get_size(v_buckets_x27_2066_);
                v___x_2072_ = lean_nat_dec_le(v___x_2070_, v___x_2071_);
                crate::leanh::lean_dec(v___x_2070_);
                if v___x_2072_ == 0 {
                    v_val_2073_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2035_,
                        v_buckets_x27_2066_,
                    );
                    if v_isShared_2062_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2061_, 1, v_val_2073_);
                        crate::leanh::lean_ctor_set(v___x_2061_, 0, v_size_x27_2064_);
                        v___x_2075_ = v___x_2061_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2078_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_size_x27_2064_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_val_2073_);
                        v___x_2075_ = v_reuseFailAlloc_2078_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2035_);
                    if v_isShared_2062_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2061_, 1, v_buckets_x27_2066_);
                        crate::leanh::lean_ctor_set(v___x_2061_, 0, v_size_x27_2064_);
                        v___x_2080_ = v___x_2061_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_size_x27_2064_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_buckets_x27_2066_);
                        v___x_2080_ = v_reuseFailAlloc_2083_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2076_ = crate::leanh::lean_box((v___x_2059_) as usize);
                v___x_2077_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2077_, 0, v___x_2076_);
                crate::leanh::lean_ctor_set(v___x_2077_, 1, v___x_2075_);
                return v___x_2077_;
            }
            3 => {
                v___x_2081_ = crate::leanh::lean_box((v___x_2059_) as usize);
                v___x_2082_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2082_, 0, v___x_2081_);
                crate::leanh::lean_ctor_set(v___x_2082_, 1, v___x_2080_);
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getThenInsertIfNew_x3f___redArg(
    mut v_x_2089_: *mut crate::leanh::LeanObject,
    mut v_x_2090_: *mut crate::leanh::LeanObject,
    mut v_m_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v_b_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: u64 = 0;
    let mut v___x_2099_: u64 = 0;
    let mut v___x_2100_: u64 = 0;
    let mut v___x_2101_: u64 = 0;
    let mut v_fold_2102_: u64 = 0;
    let mut v___x_2103_: u64 = 0;
    let mut v___x_2104_: u64 = 0;
    let mut v___x_2105_: u64 = 0;
    let mut v___x_2106_: usize = 0;
    let mut v___x_2107_: usize = 0;
    let mut v___x_2108_: usize = 0;
    let mut v___x_2109_: usize = 0;
    let mut v___x_2110_: usize = 0;
    let mut v_bkt_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: u8 = 0;
    let mut v_val_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2094_ = crate::leanh::lean_ctor_get(v_m_2091_, 0);
                v_buckets_2095_ = crate::leanh::lean_ctor_get(v_m_2091_, 1);
                v___x_2096_ = lean_array_get_size(v_buckets_2095_);
                crate::leanh::lean_inc_ref(v_x_2090_);
                crate::leanh::lean_inc_n(v_a_2092_, 2);
                v___x_2097_ = crate::leanh::lean_apply_1(v_x_2090_, v_a_2092_);
                v___x_2098_ = 32u64;
                v___x_2099_ = crate::leanh::lean_unbox_uint64(v___x_2097_);
                v___x_2100_ = lean_uint64_shift_right(v___x_2099_, v___x_2098_);
                v___x_2101_ = crate::leanh::lean_unbox_uint64(v___x_2097_);
                crate::leanh::lean_dec_ref(v___x_2097_);
                v_fold_2102_ = lean_uint64_xor(v___x_2101_, v___x_2100_);
                v___x_2103_ = 16u64;
                v___x_2104_ = lean_uint64_shift_right(v_fold_2102_, v___x_2103_);
                v___x_2105_ = lean_uint64_xor(v_fold_2102_, v___x_2104_);
                v___x_2106_ = lean_uint64_to_usize(v___x_2105_);
                v___x_2107_ = lean_usize_of_nat(v___x_2096_);
                v___x_2108_ = 1usize;
                v___x_2109_ = lean_usize_sub(v___x_2107_, v___x_2108_);
                v___x_2110_ = lean_usize_land(v___x_2106_, v___x_2109_);
                v_bkt_2111_ = lean_array_uget_borrowed(v_buckets_2095_, v___x_2110_);
                crate::leanh::lean_inc(v_bkt_2111_);
                v___x_2112_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_x_2089_,
                    v_a_2092_,
                    v_bkt_2111_,
                );
                if crate::leanh::lean_obj_tag(v___x_2112_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2095_);
                    crate::leanh::lean_inc(v_size_2094_);
                    v_isSharedCheck_2135_ = (!crate::leanh::lean_is_exclusive(v_m_2091_)) as u8;
                    if v_isSharedCheck_2135_ == 0 {
                        v_unused_2136_ = crate::leanh::lean_ctor_get(v_m_2091_, 1);
                        crate::leanh::lean_dec(v_unused_2136_);
                        v_unused_2137_ = crate::leanh::lean_ctor_get(v_m_2091_, 0);
                        crate::leanh::lean_dec(v_unused_2137_);
                        v___x_2114_ = v_m_2091_;
                        v_isShared_2115_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2091_);
                        v___x_2114_ = crate::leanh::lean_box(0);
                        v_isShared_2115_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2093_);
                    crate::leanh::lean_dec(v_a_2092_);
                    crate::leanh::lean_dec_ref(v_x_2090_);
                    v___x_2138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2112_);
                    crate::leanh::lean_ctor_set(v___x_2138_, 1, v_m_2091_);
                    return v___x_2138_;
                }
            }
            1 => {
                v___x_2116_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2117_ = lean_nat_add(v_size_2094_, v___x_2116_);
                crate::leanh::lean_dec(v_size_2094_);
                crate::leanh::lean_inc(v_bkt_2111_);
                v___x_2118_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2118_, 0, v_a_2092_);
                crate::leanh::lean_ctor_set(v___x_2118_, 1, v_b_2093_);
                crate::leanh::lean_ctor_set(v___x_2118_, 2, v_bkt_2111_);
                v_buckets_x27_2119_ = lean_array_uset(v_buckets_2095_, v___x_2110_, v___x_2118_);
                v___x_2120_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2121_ = lean_nat_mul(v_size_x27_2117_, v___x_2120_);
                v___x_2122_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2123_ = lean_nat_div(v___x_2121_, v___x_2122_);
                crate::leanh::lean_dec(v___x_2121_);
                v___x_2124_ = lean_array_get_size(v_buckets_x27_2119_);
                v___x_2125_ = lean_nat_dec_le(v___x_2123_, v___x_2124_);
                crate::leanh::lean_dec(v___x_2123_);
                if v___x_2125_ == 0 {
                    v_val_2126_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2090_,
                        v_buckets_x27_2119_,
                    );
                    if v_isShared_2115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2114_, 1, v_val_2126_);
                        crate::leanh::lean_ctor_set(v___x_2114_, 0, v_size_x27_2117_);
                        v___x_2128_ = v___x_2114_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2130_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_size_x27_2117_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_val_2126_);
                        v___x_2128_ = v_reuseFailAlloc_2130_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2090_);
                    if v_isShared_2115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2114_, 1, v_buckets_x27_2119_);
                        crate::leanh::lean_ctor_set(v___x_2114_, 0, v_size_x27_2117_);
                        v___x_2132_ = v___x_2114_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2134_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_size_x27_2117_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_buckets_x27_2119_);
                        v___x_2132_ = v_reuseFailAlloc_2134_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2129_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2129_, 0, v___x_2112_);
                crate::leanh::lean_ctor_set(v___x_2129_, 1, v___x_2128_);
                return v___x_2129_;
            }
            3 => {
                v___x_2133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2112_);
                crate::leanh::lean_ctor_set(v___x_2133_, 1, v___x_2132_);
                return v___x_2133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2139_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2140_: *mut crate::leanh::LeanObject,
    mut v_x_2141_: *mut crate::leanh::LeanObject,
    mut v_x_2142_: *mut crate::leanh::LeanObject,
    mut v_inst_2143_: *mut crate::leanh::LeanObject,
    mut v_m_2144_: *mut crate::leanh::LeanObject,
    mut v_a_2145_: *mut crate::leanh::LeanObject,
    mut v_b_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u64 = 0;
    let mut v___x_2152_: u64 = 0;
    let mut v___x_2153_: u64 = 0;
    let mut v___x_2154_: u64 = 0;
    let mut v_fold_2155_: u64 = 0;
    let mut v___x_2156_: u64 = 0;
    let mut v___x_2157_: u64 = 0;
    let mut v___x_2158_: u64 = 0;
    let mut v___x_2159_: usize = 0;
    let mut v___x_2160_: usize = 0;
    let mut v___x_2161_: usize = 0;
    let mut v___x_2162_: usize = 0;
    let mut v___x_2163_: usize = 0;
    let mut v_bkt_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    let mut v_val_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_unused_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2147_ = crate::leanh::lean_ctor_get(v_m_2144_, 0);
                v_buckets_2148_ = crate::leanh::lean_ctor_get(v_m_2144_, 1);
                v___x_2149_ = lean_array_get_size(v_buckets_2148_);
                crate::leanh::lean_inc_ref(v_x_2142_);
                crate::leanh::lean_inc_n(v_a_2145_, 2);
                v___x_2150_ = crate::leanh::lean_apply_1(v_x_2142_, v_a_2145_);
                v___x_2151_ = 32u64;
                v___x_2152_ = crate::leanh::lean_unbox_uint64(v___x_2150_);
                v___x_2153_ = lean_uint64_shift_right(v___x_2152_, v___x_2151_);
                v___x_2154_ = crate::leanh::lean_unbox_uint64(v___x_2150_);
                crate::leanh::lean_dec_ref(v___x_2150_);
                v_fold_2155_ = lean_uint64_xor(v___x_2154_, v___x_2153_);
                v___x_2156_ = 16u64;
                v___x_2157_ = lean_uint64_shift_right(v_fold_2155_, v___x_2156_);
                v___x_2158_ = lean_uint64_xor(v_fold_2155_, v___x_2157_);
                v___x_2159_ = lean_uint64_to_usize(v___x_2158_);
                v___x_2160_ = lean_usize_of_nat(v___x_2149_);
                v___x_2161_ = 1usize;
                v___x_2162_ = lean_usize_sub(v___x_2160_, v___x_2161_);
                v___x_2163_ = lean_usize_land(v___x_2159_, v___x_2162_);
                v_bkt_2164_ = lean_array_uget_borrowed(v_buckets_2148_, v___x_2163_);
                crate::leanh::lean_inc(v_bkt_2164_);
                v___x_2165_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_x_2141_,
                    v_a_2145_,
                    v_bkt_2164_,
                );
                if crate::leanh::lean_obj_tag(v___x_2165_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2148_);
                    crate::leanh::lean_inc(v_size_2147_);
                    v_isSharedCheck_2188_ = (!crate::leanh::lean_is_exclusive(v_m_2144_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v_unused_2189_ = crate::leanh::lean_ctor_get(v_m_2144_, 1);
                        crate::leanh::lean_dec(v_unused_2189_);
                        v_unused_2190_ = crate::leanh::lean_ctor_get(v_m_2144_, 0);
                        crate::leanh::lean_dec(v_unused_2190_);
                        v___x_2167_ = v_m_2144_;
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2144_);
                        v___x_2167_ = crate::leanh::lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2146_);
                    crate::leanh::lean_dec(v_a_2145_);
                    crate::leanh::lean_dec_ref(v_x_2142_);
                    v___x_2191_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2191_, 0, v___x_2165_);
                    crate::leanh::lean_ctor_set(v___x_2191_, 1, v_m_2144_);
                    return v___x_2191_;
                }
            }
            1 => {
                v___x_2169_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2170_ = lean_nat_add(v_size_2147_, v___x_2169_);
                crate::leanh::lean_dec(v_size_2147_);
                crate::leanh::lean_inc(v_bkt_2164_);
                v___x_2171_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2171_, 0, v_a_2145_);
                crate::leanh::lean_ctor_set(v___x_2171_, 1, v_b_2146_);
                crate::leanh::lean_ctor_set(v___x_2171_, 2, v_bkt_2164_);
                v_buckets_x27_2172_ = lean_array_uset(v_buckets_2148_, v___x_2163_, v___x_2171_);
                v___x_2173_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2174_ = lean_nat_mul(v_size_x27_2170_, v___x_2173_);
                v___x_2175_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2176_ = lean_nat_div(v___x_2174_, v___x_2175_);
                crate::leanh::lean_dec(v___x_2174_);
                v___x_2177_ = lean_array_get_size(v_buckets_x27_2172_);
                v___x_2178_ = lean_nat_dec_le(v___x_2176_, v___x_2177_);
                crate::leanh::lean_dec(v___x_2176_);
                if v___x_2178_ == 0 {
                    v_val_2179_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2142_,
                        v_buckets_x27_2172_,
                    );
                    if v_isShared_2168_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2167_, 1, v_val_2179_);
                        crate::leanh::lean_ctor_set(v___x_2167_, 0, v_size_x27_2170_);
                        v___x_2181_ = v___x_2167_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_size_x27_2170_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_val_2179_);
                        v___x_2181_ = v_reuseFailAlloc_2183_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2142_);
                    if v_isShared_2168_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2167_, 1, v_buckets_x27_2172_);
                        crate::leanh::lean_ctor_set(v___x_2167_, 0, v_size_x27_2170_);
                        v___x_2185_ = v___x_2167_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2187_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_size_x27_2170_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_buckets_x27_2172_);
                        v___x_2185_ = v_reuseFailAlloc_2187_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2182_, 0, v___x_2165_);
                crate::leanh::lean_ctor_set(v___x_2182_, 1, v___x_2181_);
                return v___x_2182_;
            }
            3 => {
                v___x_2186_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2186_, 0, v___x_2165_);
                crate::leanh::lean_ctor_set(v___x_2186_, 1, v___x_2185_);
                return v___x_2186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___redArg(
    mut v_x_2192_: *mut crate::leanh::LeanObject,
    mut v_x_2193_: *mut crate::leanh::LeanObject,
    mut v_m_2194_: *mut crate::leanh::LeanObject,
    mut v_a_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_x_2192_, v_x_2193_, v_m_2194_, v_a_2195_,
    );
    return v___x_2196_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___redArg___boxed(
    mut v_x_2197_: *mut crate::leanh::LeanObject,
    mut v_x_2198_: *mut crate::leanh::LeanObject,
    mut v_m_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Std_ExtDHashMap_get_x3f___redArg(v_x_2197_, v_x_2198_, v_m_2199_, v_a_2200_);
    crate::leanh::lean_dec(v_m_2199_);
    return v_res_2201_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f(
    mut v_00_u03b1_2202_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2203_: *mut crate::leanh::LeanObject,
    mut v_x_2204_: *mut crate::leanh::LeanObject,
    mut v_x_2205_: *mut crate::leanh::LeanObject,
    mut v_inst_2206_: *mut crate::leanh::LeanObject,
    mut v_m_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2209_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_x_2204_, v_x_2205_, v_m_2207_, v_a_2208_,
    );
    return v___x_2209_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___boxed(
    mut v_00_u03b1_2210_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2211_: *mut crate::leanh::LeanObject,
    mut v_x_2212_: *mut crate::leanh::LeanObject,
    mut v_x_2213_: *mut crate::leanh::LeanObject,
    mut v_inst_2214_: *mut crate::leanh::LeanObject,
    mut v_m_2215_: *mut crate::leanh::LeanObject,
    mut v_a_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2217_ = l_Std_ExtDHashMap_get_x3f(
        v_00_u03b1_2210_,
        v_00_u03b2_2211_,
        v_x_2212_,
        v_x_2213_,
        v_inst_2214_,
        v_m_2215_,
        v_a_2216_,
    );
    crate::leanh::lean_dec(v_m_2215_);
    return v_res_2217_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___redArg(
    mut v_x_2218_: *mut crate::leanh::LeanObject,
    mut v_x_2219_: *mut crate::leanh::LeanObject,
    mut v_m_2220_: *mut crate::leanh::LeanObject,
    mut v_a_2221_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2222_: u8 = 0;
    v___x_2222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2218_, v_x_2219_, v_m_2220_, v_a_2221_,
    );
    return v___x_2222_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___redArg___boxed(
    mut v_x_2223_: *mut crate::leanh::LeanObject,
    mut v_x_2224_: *mut crate::leanh::LeanObject,
    mut v_m_2225_: *mut crate::leanh::LeanObject,
    mut v_a_2226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2227_: u8 = 0;
    let mut v_r_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2227_ = l_Std_ExtDHashMap_contains___redArg(v_x_2223_, v_x_2224_, v_m_2225_, v_a_2226_);
    crate::leanh::lean_dec(v_m_2225_);
    v_r_2228_ = crate::leanh::lean_box((v_res_2227_) as usize);
    return v_r_2228_;
}
pub unsafe fn l_Std_ExtDHashMap_contains(
    mut v_00_u03b1_2229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2230_: *mut crate::leanh::LeanObject,
    mut v_x_2231_: *mut crate::leanh::LeanObject,
    mut v_x_2232_: *mut crate::leanh::LeanObject,
    mut v_inst_2233_: *mut crate::leanh::LeanObject,
    mut v_inst_2234_: *mut crate::leanh::LeanObject,
    mut v_m_2235_: *mut crate::leanh::LeanObject,
    mut v_a_2236_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2237_: u8 = 0;
    v___x_2237_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2231_, v_x_2232_, v_m_2235_, v_a_2236_,
    );
    return v___x_2237_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___boxed(
    mut v_00_u03b1_2238_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2239_: *mut crate::leanh::LeanObject,
    mut v_x_2240_: *mut crate::leanh::LeanObject,
    mut v_x_2241_: *mut crate::leanh::LeanObject,
    mut v_inst_2242_: *mut crate::leanh::LeanObject,
    mut v_inst_2243_: *mut crate::leanh::LeanObject,
    mut v_m_2244_: *mut crate::leanh::LeanObject,
    mut v_a_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2246_: u8 = 0;
    let mut v_r_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Std_ExtDHashMap_contains(
        v_00_u03b1_2238_,
        v_00_u03b2_2239_,
        v_x_2240_,
        v_x_2241_,
        v_inst_2242_,
        v_inst_2243_,
        v_m_2244_,
        v_a_2245_,
    );
    crate::leanh::lean_dec(v_m_2244_);
    v_r_2247_ = crate::leanh::lean_box((v_res_2246_) as usize);
    return v_r_2247_;
}
pub unsafe fn l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2248_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2249_: *mut crate::leanh::LeanObject,
    mut v_x_2250_: *mut crate::leanh::LeanObject,
    mut v_x_2251_: *mut crate::leanh::LeanObject,
    mut v_inst_2252_: *mut crate::leanh::LeanObject,
    mut v_inst_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = crate::leanh::lean_box(0);
    return v___x_2254_;
}
pub unsafe fn l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(
    mut v_00_u03b1_2255_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2256_: *mut crate::leanh::LeanObject,
    mut v_x_2257_: *mut crate::leanh::LeanObject,
    mut v_x_2258_: *mut crate::leanh::LeanObject,
    mut v_inst_2259_: *mut crate::leanh::LeanObject,
    mut v_inst_2260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(
        v_00_u03b1_2255_,
        v_00_u03b2_2256_,
        v_x_2257_,
        v_x_2258_,
        v_inst_2259_,
        v_inst_2260_,
    );
    crate::leanh::lean_dec_ref(v_x_2258_);
    crate::leanh::lean_dec_ref(v_x_2257_);
    return v_res_2261_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___redArg(
    mut v_x_2262_: *mut crate::leanh::LeanObject,
    mut v_x_2263_: *mut crate::leanh::LeanObject,
    mut v_m_2264_: *mut crate::leanh::LeanObject,
    mut v_a_2265_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2266_: u8 = 0;
    v___x_2266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2262_, v_x_2263_, v_m_2264_, v_a_2265_,
    );
    return v___x_2266_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___redArg___boxed(
    mut v_x_2267_: *mut crate::leanh::LeanObject,
    mut v_x_2268_: *mut crate::leanh::LeanObject,
    mut v_m_2269_: *mut crate::leanh::LeanObject,
    mut v_a_2270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2271_: u8 = 0;
    let mut v_r_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2271_ =
        l_Std_ExtDHashMap_instDecidableMem___redArg(v_x_2267_, v_x_2268_, v_m_2269_, v_a_2270_);
    crate::leanh::lean_dec(v_m_2269_);
    v_r_2272_ = crate::leanh::lean_box((v_res_2271_) as usize);
    return v_r_2272_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem(
    mut v_00_u03b1_2273_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2274_: *mut crate::leanh::LeanObject,
    mut v_x_2275_: *mut crate::leanh::LeanObject,
    mut v_x_2276_: *mut crate::leanh::LeanObject,
    mut v_inst_2277_: *mut crate::leanh::LeanObject,
    mut v_inst_2278_: *mut crate::leanh::LeanObject,
    mut v_m_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2281_: u8 = 0;
    v___x_2281_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2275_, v_x_2276_, v_m_2279_, v_a_2280_,
    );
    return v___x_2281_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___boxed(
    mut v_00_u03b1_2282_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2283_: *mut crate::leanh::LeanObject,
    mut v_x_2284_: *mut crate::leanh::LeanObject,
    mut v_x_2285_: *mut crate::leanh::LeanObject,
    mut v_inst_2286_: *mut crate::leanh::LeanObject,
    mut v_inst_2287_: *mut crate::leanh::LeanObject,
    mut v_m_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2290_: u8 = 0;
    let mut v_r_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Std_ExtDHashMap_instDecidableMem(
        v_00_u03b1_2282_,
        v_00_u03b2_2283_,
        v_x_2284_,
        v_x_2285_,
        v_inst_2286_,
        v_inst_2287_,
        v_m_2288_,
        v_a_2289_,
    );
    crate::leanh::lean_dec(v_m_2288_);
    v_r_2291_ = crate::leanh::lean_box((v_res_2290_) as usize);
    return v_r_2291_;
}
pub unsafe fn l_Std_ExtDHashMap_get___redArg(
    mut v_x_2292_: *mut crate::leanh::LeanObject,
    mut v_x_2293_: *mut crate::leanh::LeanObject,
    mut v_m_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ =
        l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_2292_, v_x_2293_, v_m_2294_, v_a_2295_);
    return v___x_2296_;
}
pub unsafe fn l_Std_ExtDHashMap_get___redArg___boxed(
    mut v_x_2297_: *mut crate::leanh::LeanObject,
    mut v_x_2298_: *mut crate::leanh::LeanObject,
    mut v_m_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Std_ExtDHashMap_get___redArg(v_x_2297_, v_x_2298_, v_m_2299_, v_a_2300_);
    crate::leanh::lean_dec(v_m_2299_);
    return v_res_2301_;
}
pub unsafe fn l_Std_ExtDHashMap_get(
    mut v_00_u03b1_2302_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2303_: *mut crate::leanh::LeanObject,
    mut v_x_2304_: *mut crate::leanh::LeanObject,
    mut v_x_2305_: *mut crate::leanh::LeanObject,
    mut v_inst_2306_: *mut crate::leanh::LeanObject,
    mut v_m_2307_: *mut crate::leanh::LeanObject,
    mut v_a_2308_: *mut crate::leanh::LeanObject,
    mut v_h_2309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ =
        l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_2304_, v_x_2305_, v_m_2307_, v_a_2308_);
    return v___x_2310_;
}
pub unsafe fn l_Std_ExtDHashMap_get___boxed(
    mut v_00_u03b1_2311_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2312_: *mut crate::leanh::LeanObject,
    mut v_x_2313_: *mut crate::leanh::LeanObject,
    mut v_x_2314_: *mut crate::leanh::LeanObject,
    mut v_inst_2315_: *mut crate::leanh::LeanObject,
    mut v_m_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_h_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2319_ = l_Std_ExtDHashMap_get(
        v_00_u03b1_2311_,
        v_00_u03b2_2312_,
        v_x_2313_,
        v_x_2314_,
        v_inst_2315_,
        v_m_2316_,
        v_a_2317_,
        v_h_2318_,
    );
    crate::leanh::lean_dec(v_m_2316_);
    return v_res_2319_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x21___redArg(
    mut v_x_2320_: *mut crate::leanh::LeanObject,
    mut v_x_2321_: *mut crate::leanh::LeanObject,
    mut v_m_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
    mut v_inst_2324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
        v_x_2320_,
        v_x_2321_,
        v_m_2322_,
        v_a_2323_,
        v_inst_2324_,
    );
    return v___x_2325_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x21___redArg___boxed(
    mut v_x_2326_: *mut crate::leanh::LeanObject,
    mut v_x_2327_: *mut crate::leanh::LeanObject,
    mut v_m_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_inst_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Std_ExtDHashMap_get_x21___redArg(
        v_x_2326_,
        v_x_2327_,
        v_m_2328_,
        v_a_2329_,
        v_inst_2330_,
    );
    crate::leanh::lean_dec(v_inst_2330_);
    crate::leanh::lean_dec(v_m_2328_);
    return v_res_2331_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x21(
    mut v_00_u03b1_2332_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2333_: *mut crate::leanh::LeanObject,
    mut v_x_2334_: *mut crate::leanh::LeanObject,
    mut v_x_2335_: *mut crate::leanh::LeanObject,
    mut v_inst_2336_: *mut crate::leanh::LeanObject,
    mut v_m_2337_: *mut crate::leanh::LeanObject,
    mut v_a_2338_: *mut crate::leanh::LeanObject,
    mut v_inst_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2340_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
        v_x_2334_,
        v_x_2335_,
        v_m_2337_,
        v_a_2338_,
        v_inst_2339_,
    );
    return v___x_2340_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x21___boxed(
    mut v_00_u03b1_2341_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2342_: *mut crate::leanh::LeanObject,
    mut v_x_2343_: *mut crate::leanh::LeanObject,
    mut v_x_2344_: *mut crate::leanh::LeanObject,
    mut v_inst_2345_: *mut crate::leanh::LeanObject,
    mut v_m_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
    mut v_inst_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Std_ExtDHashMap_get_x21(
        v_00_u03b1_2341_,
        v_00_u03b2_2342_,
        v_x_2343_,
        v_x_2344_,
        v_inst_2345_,
        v_m_2346_,
        v_a_2347_,
        v_inst_2348_,
    );
    crate::leanh::lean_dec(v_inst_2348_);
    crate::leanh::lean_dec(v_m_2346_);
    return v_res_2349_;
}
pub unsafe fn l_Std_ExtDHashMap_getD___redArg(
    mut v_x_2350_: *mut crate::leanh::LeanObject,
    mut v_x_2351_: *mut crate::leanh::LeanObject,
    mut v_m_2352_: *mut crate::leanh::LeanObject,
    mut v_a_2353_: *mut crate::leanh::LeanObject,
    mut v_fallback_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
        v_x_2350_,
        v_x_2351_,
        v_m_2352_,
        v_a_2353_,
        v_fallback_2354_,
    );
    return v___x_2355_;
}
pub unsafe fn l_Std_ExtDHashMap_getD___redArg___boxed(
    mut v_x_2356_: *mut crate::leanh::LeanObject,
    mut v_x_2357_: *mut crate::leanh::LeanObject,
    mut v_m_2358_: *mut crate::leanh::LeanObject,
    mut v_a_2359_: *mut crate::leanh::LeanObject,
    mut v_fallback_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2361_ = l_Std_ExtDHashMap_getD___redArg(
        v_x_2356_,
        v_x_2357_,
        v_m_2358_,
        v_a_2359_,
        v_fallback_2360_,
    );
    crate::leanh::lean_dec(v_fallback_2360_);
    crate::leanh::lean_dec(v_m_2358_);
    return v_res_2361_;
}
pub unsafe fn l_Std_ExtDHashMap_getD(
    mut v_00_u03b1_2362_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2363_: *mut crate::leanh::LeanObject,
    mut v_x_2364_: *mut crate::leanh::LeanObject,
    mut v_x_2365_: *mut crate::leanh::LeanObject,
    mut v_inst_2366_: *mut crate::leanh::LeanObject,
    mut v_m_2367_: *mut crate::leanh::LeanObject,
    mut v_a_2368_: *mut crate::leanh::LeanObject,
    mut v_fallback_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2370_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
        v_x_2364_,
        v_x_2365_,
        v_m_2367_,
        v_a_2368_,
        v_fallback_2369_,
    );
    return v___x_2370_;
}
pub unsafe fn l_Std_ExtDHashMap_getD___boxed(
    mut v_00_u03b1_2371_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2372_: *mut crate::leanh::LeanObject,
    mut v_x_2373_: *mut crate::leanh::LeanObject,
    mut v_x_2374_: *mut crate::leanh::LeanObject,
    mut v_inst_2375_: *mut crate::leanh::LeanObject,
    mut v_m_2376_: *mut crate::leanh::LeanObject,
    mut v_a_2377_: *mut crate::leanh::LeanObject,
    mut v_fallback_2378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2379_ = l_Std_ExtDHashMap_getD(
        v_00_u03b1_2371_,
        v_00_u03b2_2372_,
        v_x_2373_,
        v_x_2374_,
        v_inst_2375_,
        v_m_2376_,
        v_a_2377_,
        v_fallback_2378_,
    );
    crate::leanh::lean_dec(v_fallback_2378_);
    crate::leanh::lean_dec(v_m_2376_);
    return v_res_2379_;
}
pub unsafe fn l_Std_ExtDHashMap_erase___redArg(
    mut v_x_2380_: *mut crate::leanh::LeanObject,
    mut v_x_2381_: *mut crate::leanh::LeanObject,
    mut v_m_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_2380_, v_x_2381_, v_m_2382_, v_a_2383_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Std_ExtDHashMap_erase(
    mut v_00_u03b1_2385_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2386_: *mut crate::leanh::LeanObject,
    mut v_x_2387_: *mut crate::leanh::LeanObject,
    mut v_x_2388_: *mut crate::leanh::LeanObject,
    mut v_inst_2389_: *mut crate::leanh::LeanObject,
    mut v_inst_2390_: *mut crate::leanh::LeanObject,
    mut v_m_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_2387_, v_x_2388_, v_m_2391_, v_a_2392_,
    );
    return v___x_2393_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___redArg(
    mut v_x_2394_: *mut crate::leanh::LeanObject,
    mut v_x_2395_: *mut crate::leanh::LeanObject,
    mut v_m_2396_: *mut crate::leanh::LeanObject,
    mut v_a_2397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2398_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_2394_, v_x_2395_, v_m_2396_, v_a_2397_,
    );
    return v___x_2398_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___redArg___boxed(
    mut v_x_2399_: *mut crate::leanh::LeanObject,
    mut v_x_2400_: *mut crate::leanh::LeanObject,
    mut v_m_2401_: *mut crate::leanh::LeanObject,
    mut v_a_2402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2403_ =
        l_Std_ExtDHashMap_Const_get_x3f___redArg(v_x_2399_, v_x_2400_, v_m_2401_, v_a_2402_);
    crate::leanh::lean_dec(v_m_2401_);
    return v_res_2403_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f(
    mut v_00_u03b1_2404_: *mut crate::leanh::LeanObject,
    mut v_x_2405_: *mut crate::leanh::LeanObject,
    mut v_x_2406_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2407_: *mut crate::leanh::LeanObject,
    mut v_inst_2408_: *mut crate::leanh::LeanObject,
    mut v_inst_2409_: *mut crate::leanh::LeanObject,
    mut v_m_2410_: *mut crate::leanh::LeanObject,
    mut v_a_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_2405_, v_x_2406_, v_m_2410_, v_a_2411_,
    );
    return v___x_2412_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___boxed(
    mut v_00_u03b1_2413_: *mut crate::leanh::LeanObject,
    mut v_x_2414_: *mut crate::leanh::LeanObject,
    mut v_x_2415_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2416_: *mut crate::leanh::LeanObject,
    mut v_inst_2417_: *mut crate::leanh::LeanObject,
    mut v_inst_2418_: *mut crate::leanh::LeanObject,
    mut v_m_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2421_ = l_Std_ExtDHashMap_Const_get_x3f(
        v_00_u03b1_2413_,
        v_x_2414_,
        v_x_2415_,
        v_00_u03b2_2416_,
        v_inst_2417_,
        v_inst_2418_,
        v_m_2419_,
        v_a_2420_,
    );
    crate::leanh::lean_dec(v_m_2419_);
    return v_res_2421_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___redArg(
    mut v_x_2422_: *mut crate::leanh::LeanObject,
    mut v_x_2423_: *mut crate::leanh::LeanObject,
    mut v_m_2424_: *mut crate::leanh::LeanObject,
    mut v_a_2425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_2422_, v_x_2423_, v_m_2424_, v_a_2425_,
    );
    return v___x_2426_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___redArg___boxed(
    mut v_x_2427_: *mut crate::leanh::LeanObject,
    mut v_x_2428_: *mut crate::leanh::LeanObject,
    mut v_m_2429_: *mut crate::leanh::LeanObject,
    mut v_a_2430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Std_ExtDHashMap_Const_get___redArg(v_x_2427_, v_x_2428_, v_m_2429_, v_a_2430_);
    crate::leanh::lean_dec(v_m_2429_);
    return v_res_2431_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get(
    mut v_00_u03b1_2432_: *mut crate::leanh::LeanObject,
    mut v_x_2433_: *mut crate::leanh::LeanObject,
    mut v_x_2434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2435_: *mut crate::leanh::LeanObject,
    mut v_inst_2436_: *mut crate::leanh::LeanObject,
    mut v_inst_2437_: *mut crate::leanh::LeanObject,
    mut v_m_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
    mut v_h_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_2433_, v_x_2434_, v_m_2438_, v_a_2439_,
    );
    return v___x_2441_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___boxed(
    mut v_00_u03b1_2442_: *mut crate::leanh::LeanObject,
    mut v_x_2443_: *mut crate::leanh::LeanObject,
    mut v_x_2444_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2445_: *mut crate::leanh::LeanObject,
    mut v_inst_2446_: *mut crate::leanh::LeanObject,
    mut v_inst_2447_: *mut crate::leanh::LeanObject,
    mut v_m_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
    mut v_h_2450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2451_ = l_Std_ExtDHashMap_Const_get(
        v_00_u03b1_2442_,
        v_x_2443_,
        v_x_2444_,
        v_00_u03b2_2445_,
        v_inst_2446_,
        v_inst_2447_,
        v_m_2448_,
        v_a_2449_,
        v_h_2450_,
    );
    crate::leanh::lean_dec(v_m_2448_);
    return v_res_2451_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getD___redArg(
    mut v_x_2452_: *mut crate::leanh::LeanObject,
    mut v_x_2453_: *mut crate::leanh::LeanObject,
    mut v_m_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_fallback_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_x_2452_,
        v_x_2453_,
        v_m_2454_,
        v_a_2455_,
        v_fallback_2456_,
    );
    return v___x_2457_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getD___redArg___boxed(
    mut v_x_2458_: *mut crate::leanh::LeanObject,
    mut v_x_2459_: *mut crate::leanh::LeanObject,
    mut v_m_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_fallback_2462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2463_ = l_Std_ExtDHashMap_Const_getD___redArg(
        v_x_2458_,
        v_x_2459_,
        v_m_2460_,
        v_a_2461_,
        v_fallback_2462_,
    );
    crate::leanh::lean_dec(v_fallback_2462_);
    crate::leanh::lean_dec(v_m_2460_);
    return v_res_2463_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getD(
    mut v_00_u03b1_2464_: *mut crate::leanh::LeanObject,
    mut v_x_2465_: *mut crate::leanh::LeanObject,
    mut v_x_2466_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2467_: *mut crate::leanh::LeanObject,
    mut v_inst_2468_: *mut crate::leanh::LeanObject,
    mut v_inst_2469_: *mut crate::leanh::LeanObject,
    mut v_m_2470_: *mut crate::leanh::LeanObject,
    mut v_a_2471_: *mut crate::leanh::LeanObject,
    mut v_fallback_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_x_2465_,
        v_x_2466_,
        v_m_2470_,
        v_a_2471_,
        v_fallback_2472_,
    );
    return v___x_2473_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getD___boxed(
    mut v_00_u03b1_2474_: *mut crate::leanh::LeanObject,
    mut v_x_2475_: *mut crate::leanh::LeanObject,
    mut v_x_2476_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2477_: *mut crate::leanh::LeanObject,
    mut v_inst_2478_: *mut crate::leanh::LeanObject,
    mut v_inst_2479_: *mut crate::leanh::LeanObject,
    mut v_m_2480_: *mut crate::leanh::LeanObject,
    mut v_a_2481_: *mut crate::leanh::LeanObject,
    mut v_fallback_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2483_ = l_Std_ExtDHashMap_Const_getD(
        v_00_u03b1_2474_,
        v_x_2475_,
        v_x_2476_,
        v_00_u03b2_2477_,
        v_inst_2478_,
        v_inst_2479_,
        v_m_2480_,
        v_a_2481_,
        v_fallback_2482_,
    );
    crate::leanh::lean_dec(v_fallback_2482_);
    crate::leanh::lean_dec(v_m_2480_);
    return v_res_2483_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x21___redArg(
    mut v_x_2484_: *mut crate::leanh::LeanObject,
    mut v_x_2485_: *mut crate::leanh::LeanObject,
    mut v_inst_2486_: *mut crate::leanh::LeanObject,
    mut v_m_2487_: *mut crate::leanh::LeanObject,
    mut v_a_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_x_2484_,
        v_x_2485_,
        v_inst_2486_,
        v_m_2487_,
        v_a_2488_,
    );
    return v___x_2489_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x21___redArg___boxed(
    mut v_x_2490_: *mut crate::leanh::LeanObject,
    mut v_x_2491_: *mut crate::leanh::LeanObject,
    mut v_inst_2492_: *mut crate::leanh::LeanObject,
    mut v_m_2493_: *mut crate::leanh::LeanObject,
    mut v_a_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_Std_ExtDHashMap_Const_get_x21___redArg(
        v_x_2490_,
        v_x_2491_,
        v_inst_2492_,
        v_m_2493_,
        v_a_2494_,
    );
    crate::leanh::lean_dec(v_m_2493_);
    crate::leanh::lean_dec(v_inst_2492_);
    return v_res_2495_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x21(
    mut v_00_u03b1_2496_: *mut crate::leanh::LeanObject,
    mut v_x_2497_: *mut crate::leanh::LeanObject,
    mut v_x_2498_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2499_: *mut crate::leanh::LeanObject,
    mut v_inst_2500_: *mut crate::leanh::LeanObject,
    mut v_inst_2501_: *mut crate::leanh::LeanObject,
    mut v_inst_2502_: *mut crate::leanh::LeanObject,
    mut v_m_2503_: *mut crate::leanh::LeanObject,
    mut v_a_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_x_2497_,
        v_x_2498_,
        v_inst_2502_,
        v_m_2503_,
        v_a_2504_,
    );
    return v___x_2505_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x21___boxed(
    mut v_00_u03b1_2506_: *mut crate::leanh::LeanObject,
    mut v_x_2507_: *mut crate::leanh::LeanObject,
    mut v_x_2508_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2509_: *mut crate::leanh::LeanObject,
    mut v_inst_2510_: *mut crate::leanh::LeanObject,
    mut v_inst_2511_: *mut crate::leanh::LeanObject,
    mut v_inst_2512_: *mut crate::leanh::LeanObject,
    mut v_m_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Std_ExtDHashMap_Const_get_x21(
        v_00_u03b1_2506_,
        v_x_2507_,
        v_x_2508_,
        v_00_u03b2_2509_,
        v_inst_2510_,
        v_inst_2511_,
        v_inst_2512_,
        v_m_2513_,
        v_a_2514_,
    );
    crate::leanh::lean_dec(v_m_2513_);
    crate::leanh::lean_dec(v_inst_2512_);
    return v_res_2515_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f___redArg(
    mut v_x_2516_: *mut crate::leanh::LeanObject,
    mut v_x_2517_: *mut crate::leanh::LeanObject,
    mut v_m_2518_: *mut crate::leanh::LeanObject,
    mut v_a_2519_: *mut crate::leanh::LeanObject,
    mut v_b_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: u64 = 0;
    let mut v___x_2526_: u64 = 0;
    let mut v___x_2527_: u64 = 0;
    let mut v___x_2528_: u64 = 0;
    let mut v_fold_2529_: u64 = 0;
    let mut v___x_2530_: u64 = 0;
    let mut v___x_2531_: u64 = 0;
    let mut v___x_2532_: u64 = 0;
    let mut v___x_2533_: usize = 0;
    let mut v___x_2534_: usize = 0;
    let mut v___x_2535_: usize = 0;
    let mut v___x_2536_: usize = 0;
    let mut v___x_2537_: usize = 0;
    let mut v_bkt_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v_val_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2562_: u8 = 0;
    let mut v_unused_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2521_ = crate::leanh::lean_ctor_get(v_m_2518_, 0);
                v_buckets_2522_ = crate::leanh::lean_ctor_get(v_m_2518_, 1);
                v___x_2523_ = lean_array_get_size(v_buckets_2522_);
                crate::leanh::lean_inc_ref(v_x_2517_);
                crate::leanh::lean_inc_n(v_a_2519_, 2);
                v___x_2524_ = crate::leanh::lean_apply_1(v_x_2517_, v_a_2519_);
                v___x_2525_ = 32u64;
                v___x_2526_ = crate::leanh::lean_unbox_uint64(v___x_2524_);
                v___x_2527_ = lean_uint64_shift_right(v___x_2526_, v___x_2525_);
                v___x_2528_ = crate::leanh::lean_unbox_uint64(v___x_2524_);
                crate::leanh::lean_dec_ref(v___x_2524_);
                v_fold_2529_ = lean_uint64_xor(v___x_2528_, v___x_2527_);
                v___x_2530_ = 16u64;
                v___x_2531_ = lean_uint64_shift_right(v_fold_2529_, v___x_2530_);
                v___x_2532_ = lean_uint64_xor(v_fold_2529_, v___x_2531_);
                v___x_2533_ = lean_uint64_to_usize(v___x_2532_);
                v___x_2534_ = lean_usize_of_nat(v___x_2523_);
                v___x_2535_ = 1usize;
                v___x_2536_ = lean_usize_sub(v___x_2534_, v___x_2535_);
                v___x_2537_ = lean_usize_land(v___x_2533_, v___x_2536_);
                v_bkt_2538_ = lean_array_uget_borrowed(v_buckets_2522_, v___x_2537_);
                crate::leanh::lean_inc(v_bkt_2538_);
                v___x_2539_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_2516_,
                    v_a_2519_,
                    v_bkt_2538_,
                );
                if crate::leanh::lean_obj_tag(v___x_2539_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2522_);
                    crate::leanh::lean_inc(v_size_2521_);
                    v_isSharedCheck_2562_ = (!crate::leanh::lean_is_exclusive(v_m_2518_)) as u8;
                    if v_isSharedCheck_2562_ == 0 {
                        v_unused_2563_ = crate::leanh::lean_ctor_get(v_m_2518_, 1);
                        crate::leanh::lean_dec(v_unused_2563_);
                        v_unused_2564_ = crate::leanh::lean_ctor_get(v_m_2518_, 0);
                        crate::leanh::lean_dec(v_unused_2564_);
                        v___x_2541_ = v_m_2518_;
                        v_isShared_2542_ = v_isSharedCheck_2562_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2518_);
                        v___x_2541_ = crate::leanh::lean_box(0);
                        v_isShared_2542_ = v_isSharedCheck_2562_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2520_);
                    crate::leanh::lean_dec(v_a_2519_);
                    crate::leanh::lean_dec_ref(v_x_2517_);
                    v___x_2565_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2565_, 0, v___x_2539_);
                    crate::leanh::lean_ctor_set(v___x_2565_, 1, v_m_2518_);
                    return v___x_2565_;
                }
            }
            1 => {
                v___x_2543_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2544_ = lean_nat_add(v_size_2521_, v___x_2543_);
                crate::leanh::lean_dec(v_size_2521_);
                crate::leanh::lean_inc(v_bkt_2538_);
                v___x_2545_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2545_, 0, v_a_2519_);
                crate::leanh::lean_ctor_set(v___x_2545_, 1, v_b_2520_);
                crate::leanh::lean_ctor_set(v___x_2545_, 2, v_bkt_2538_);
                v_buckets_x27_2546_ = lean_array_uset(v_buckets_2522_, v___x_2537_, v___x_2545_);
                v___x_2547_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2548_ = lean_nat_mul(v_size_x27_2544_, v___x_2547_);
                v___x_2549_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2550_ = lean_nat_div(v___x_2548_, v___x_2549_);
                crate::leanh::lean_dec(v___x_2548_);
                v___x_2551_ = lean_array_get_size(v_buckets_x27_2546_);
                v___x_2552_ = lean_nat_dec_le(v___x_2550_, v___x_2551_);
                crate::leanh::lean_dec(v___x_2550_);
                if v___x_2552_ == 0 {
                    v_val_2553_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2517_,
                        v_buckets_x27_2546_,
                    );
                    if v_isShared_2542_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2541_, 1, v_val_2553_);
                        crate::leanh::lean_ctor_set(v___x_2541_, 0, v_size_x27_2544_);
                        v___x_2555_ = v___x_2541_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_size_x27_2544_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_val_2553_);
                        v___x_2555_ = v_reuseFailAlloc_2557_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2517_);
                    if v_isShared_2542_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2541_, 1, v_buckets_x27_2546_);
                        crate::leanh::lean_ctor_set(v___x_2541_, 0, v_size_x27_2544_);
                        v___x_2559_ = v___x_2541_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_size_x27_2544_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_buckets_x27_2546_);
                        v___x_2559_ = v_reuseFailAlloc_2561_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2556_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2556_, 0, v___x_2539_);
                crate::leanh::lean_ctor_set(v___x_2556_, 1, v___x_2555_);
                return v___x_2556_;
            }
            3 => {
                v___x_2560_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2560_, 0, v___x_2539_);
                crate::leanh::lean_ctor_set(v___x_2560_, 1, v___x_2559_);
                return v___x_2560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2566_: *mut crate::leanh::LeanObject,
    mut v_x_2567_: *mut crate::leanh::LeanObject,
    mut v_x_2568_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2569_: *mut crate::leanh::LeanObject,
    mut v_inst_2570_: *mut crate::leanh::LeanObject,
    mut v_inst_2571_: *mut crate::leanh::LeanObject,
    mut v_m_2572_: *mut crate::leanh::LeanObject,
    mut v_a_2573_: *mut crate::leanh::LeanObject,
    mut v_b_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u64 = 0;
    let mut v___x_2580_: u64 = 0;
    let mut v___x_2581_: u64 = 0;
    let mut v___x_2582_: u64 = 0;
    let mut v_fold_2583_: u64 = 0;
    let mut v___x_2584_: u64 = 0;
    let mut v___x_2585_: u64 = 0;
    let mut v___x_2586_: u64 = 0;
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: usize = 0;
    let mut v___x_2589_: usize = 0;
    let mut v___x_2590_: usize = 0;
    let mut v___x_2591_: usize = 0;
    let mut v_bkt_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut v_val_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_unused_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2575_ = crate::leanh::lean_ctor_get(v_m_2572_, 0);
                v_buckets_2576_ = crate::leanh::lean_ctor_get(v_m_2572_, 1);
                v___x_2577_ = lean_array_get_size(v_buckets_2576_);
                crate::leanh::lean_inc_ref(v_x_2568_);
                crate::leanh::lean_inc_n(v_a_2573_, 2);
                v___x_2578_ = crate::leanh::lean_apply_1(v_x_2568_, v_a_2573_);
                v___x_2579_ = 32u64;
                v___x_2580_ = crate::leanh::lean_unbox_uint64(v___x_2578_);
                v___x_2581_ = lean_uint64_shift_right(v___x_2580_, v___x_2579_);
                v___x_2582_ = crate::leanh::lean_unbox_uint64(v___x_2578_);
                crate::leanh::lean_dec_ref(v___x_2578_);
                v_fold_2583_ = lean_uint64_xor(v___x_2582_, v___x_2581_);
                v___x_2584_ = 16u64;
                v___x_2585_ = lean_uint64_shift_right(v_fold_2583_, v___x_2584_);
                v___x_2586_ = lean_uint64_xor(v_fold_2583_, v___x_2585_);
                v___x_2587_ = lean_uint64_to_usize(v___x_2586_);
                v___x_2588_ = lean_usize_of_nat(v___x_2577_);
                v___x_2589_ = 1usize;
                v___x_2590_ = lean_usize_sub(v___x_2588_, v___x_2589_);
                v___x_2591_ = lean_usize_land(v___x_2587_, v___x_2590_);
                v_bkt_2592_ = lean_array_uget_borrowed(v_buckets_2576_, v___x_2591_);
                crate::leanh::lean_inc(v_bkt_2592_);
                v___x_2593_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_2567_,
                    v_a_2573_,
                    v_bkt_2592_,
                );
                if crate::leanh::lean_obj_tag(v___x_2593_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2576_);
                    crate::leanh::lean_inc(v_size_2575_);
                    v_isSharedCheck_2616_ = (!crate::leanh::lean_is_exclusive(v_m_2572_)) as u8;
                    if v_isSharedCheck_2616_ == 0 {
                        v_unused_2617_ = crate::leanh::lean_ctor_get(v_m_2572_, 1);
                        crate::leanh::lean_dec(v_unused_2617_);
                        v_unused_2618_ = crate::leanh::lean_ctor_get(v_m_2572_, 0);
                        crate::leanh::lean_dec(v_unused_2618_);
                        v___x_2595_ = v_m_2572_;
                        v_isShared_2596_ = v_isSharedCheck_2616_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2572_);
                        v___x_2595_ = crate::leanh::lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2616_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2574_);
                    crate::leanh::lean_dec(v_a_2573_);
                    crate::leanh::lean_dec_ref(v_x_2568_);
                    v___x_2619_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2619_, 0, v___x_2593_);
                    crate::leanh::lean_ctor_set(v___x_2619_, 1, v_m_2572_);
                    return v___x_2619_;
                }
            }
            1 => {
                v___x_2597_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2598_ = lean_nat_add(v_size_2575_, v___x_2597_);
                crate::leanh::lean_dec(v_size_2575_);
                crate::leanh::lean_inc(v_bkt_2592_);
                v___x_2599_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2599_, 0, v_a_2573_);
                crate::leanh::lean_ctor_set(v___x_2599_, 1, v_b_2574_);
                crate::leanh::lean_ctor_set(v___x_2599_, 2, v_bkt_2592_);
                v_buckets_x27_2600_ = lean_array_uset(v_buckets_2576_, v___x_2591_, v___x_2599_);
                v___x_2601_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2602_ = lean_nat_mul(v_size_x27_2598_, v___x_2601_);
                v___x_2603_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2604_ = lean_nat_div(v___x_2602_, v___x_2603_);
                crate::leanh::lean_dec(v___x_2602_);
                v___x_2605_ = lean_array_get_size(v_buckets_x27_2600_);
                v___x_2606_ = lean_nat_dec_le(v___x_2604_, v___x_2605_);
                crate::leanh::lean_dec(v___x_2604_);
                if v___x_2606_ == 0 {
                    v_val_2607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2568_,
                        v_buckets_x27_2600_,
                    );
                    if v_isShared_2596_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2595_, 1, v_val_2607_);
                        crate::leanh::lean_ctor_set(v___x_2595_, 0, v_size_x27_2598_);
                        v___x_2609_ = v___x_2595_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2611_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_size_x27_2598_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_val_2607_);
                        v___x_2609_ = v_reuseFailAlloc_2611_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2568_);
                    if v_isShared_2596_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2595_, 1, v_buckets_x27_2600_);
                        crate::leanh::lean_ctor_set(v___x_2595_, 0, v_size_x27_2598_);
                        v___x_2613_ = v___x_2595_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2615_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_size_x27_2598_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_buckets_x27_2600_);
                        v___x_2613_ = v_reuseFailAlloc_2615_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2610_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2610_, 0, v___x_2593_);
                crate::leanh::lean_ctor_set(v___x_2610_, 1, v___x_2609_);
                return v___x_2610_;
            }
            3 => {
                v___x_2614_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2593_);
                crate::leanh::lean_ctor_set(v___x_2614_, 1, v___x_2613_);
                return v___x_2614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___redArg(
    mut v_x_2620_: *mut crate::leanh::LeanObject,
    mut v_x_2621_: *mut crate::leanh::LeanObject,
    mut v_m_2622_: *mut crate::leanh::LeanObject,
    mut v_a_2623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2624_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_2620_, v_x_2621_, v_m_2622_, v_a_2623_,
    );
    return v___x_2624_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___redArg___boxed(
    mut v_x_2625_: *mut crate::leanh::LeanObject,
    mut v_x_2626_: *mut crate::leanh::LeanObject,
    mut v_m_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2629_ = l_Std_ExtDHashMap_getKey_x3f___redArg(v_x_2625_, v_x_2626_, v_m_2627_, v_a_2628_);
    crate::leanh::lean_dec(v_m_2627_);
    return v_res_2629_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f(
    mut v_00_u03b1_2630_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2631_: *mut crate::leanh::LeanObject,
    mut v_x_2632_: *mut crate::leanh::LeanObject,
    mut v_x_2633_: *mut crate::leanh::LeanObject,
    mut v_inst_2634_: *mut crate::leanh::LeanObject,
    mut v_inst_2635_: *mut crate::leanh::LeanObject,
    mut v_m_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_2632_, v_x_2633_, v_m_2636_, v_a_2637_,
    );
    return v___x_2638_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___boxed(
    mut v_00_u03b1_2639_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2640_: *mut crate::leanh::LeanObject,
    mut v_x_2641_: *mut crate::leanh::LeanObject,
    mut v_x_2642_: *mut crate::leanh::LeanObject,
    mut v_inst_2643_: *mut crate::leanh::LeanObject,
    mut v_inst_2644_: *mut crate::leanh::LeanObject,
    mut v_m_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2647_ = l_Std_ExtDHashMap_getKey_x3f(
        v_00_u03b1_2639_,
        v_00_u03b2_2640_,
        v_x_2641_,
        v_x_2642_,
        v_inst_2643_,
        v_inst_2644_,
        v_m_2645_,
        v_a_2646_,
    );
    crate::leanh::lean_dec(v_m_2645_);
    return v_res_2647_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___redArg(
    mut v_x_2648_: *mut crate::leanh::LeanObject,
    mut v_x_2649_: *mut crate::leanh::LeanObject,
    mut v_m_2650_: *mut crate::leanh::LeanObject,
    mut v_a_2651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_2648_, v_x_2649_, v_m_2650_, v_a_2651_,
    );
    return v___x_2652_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___redArg___boxed(
    mut v_x_2653_: *mut crate::leanh::LeanObject,
    mut v_x_2654_: *mut crate::leanh::LeanObject,
    mut v_m_2655_: *mut crate::leanh::LeanObject,
    mut v_a_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Std_ExtDHashMap_getKey___redArg(v_x_2653_, v_x_2654_, v_m_2655_, v_a_2656_);
    crate::leanh::lean_dec(v_m_2655_);
    return v_res_2657_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey(
    mut v_00_u03b1_2658_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2659_: *mut crate::leanh::LeanObject,
    mut v_x_2660_: *mut crate::leanh::LeanObject,
    mut v_x_2661_: *mut crate::leanh::LeanObject,
    mut v_inst_2662_: *mut crate::leanh::LeanObject,
    mut v_inst_2663_: *mut crate::leanh::LeanObject,
    mut v_m_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_h_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_2660_, v_x_2661_, v_m_2664_, v_a_2665_,
    );
    return v___x_2667_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___boxed(
    mut v_00_u03b1_2668_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2669_: *mut crate::leanh::LeanObject,
    mut v_x_2670_: *mut crate::leanh::LeanObject,
    mut v_x_2671_: *mut crate::leanh::LeanObject,
    mut v_inst_2672_: *mut crate::leanh::LeanObject,
    mut v_inst_2673_: *mut crate::leanh::LeanObject,
    mut v_m_2674_: *mut crate::leanh::LeanObject,
    mut v_a_2675_: *mut crate::leanh::LeanObject,
    mut v_h_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2677_ = l_Std_ExtDHashMap_getKey(
        v_00_u03b1_2668_,
        v_00_u03b2_2669_,
        v_x_2670_,
        v_x_2671_,
        v_inst_2672_,
        v_inst_2673_,
        v_m_2674_,
        v_a_2675_,
        v_h_2676_,
    );
    crate::leanh::lean_dec(v_m_2674_);
    return v_res_2677_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x21___redArg(
    mut v_x_2678_: *mut crate::leanh::LeanObject,
    mut v_x_2679_: *mut crate::leanh::LeanObject,
    mut v_inst_2680_: *mut crate::leanh::LeanObject,
    mut v_m_2681_: *mut crate::leanh::LeanObject,
    mut v_a_2682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_2678_,
        v_x_2679_,
        v_inst_2680_,
        v_m_2681_,
        v_a_2682_,
    );
    return v___x_2683_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x21___redArg___boxed(
    mut v_x_2684_: *mut crate::leanh::LeanObject,
    mut v_x_2685_: *mut crate::leanh::LeanObject,
    mut v_inst_2686_: *mut crate::leanh::LeanObject,
    mut v_m_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Std_ExtDHashMap_getKey_x21___redArg(
        v_x_2684_,
        v_x_2685_,
        v_inst_2686_,
        v_m_2687_,
        v_a_2688_,
    );
    crate::leanh::lean_dec(v_m_2687_);
    crate::leanh::lean_dec(v_inst_2686_);
    return v_res_2689_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x21(
    mut v_00_u03b1_2690_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2691_: *mut crate::leanh::LeanObject,
    mut v_x_2692_: *mut crate::leanh::LeanObject,
    mut v_x_2693_: *mut crate::leanh::LeanObject,
    mut v_inst_2694_: *mut crate::leanh::LeanObject,
    mut v_inst_2695_: *mut crate::leanh::LeanObject,
    mut v_inst_2696_: *mut crate::leanh::LeanObject,
    mut v_m_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2699_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_2692_,
        v_x_2693_,
        v_inst_2696_,
        v_m_2697_,
        v_a_2698_,
    );
    return v___x_2699_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x21___boxed(
    mut v_00_u03b1_2700_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2701_: *mut crate::leanh::LeanObject,
    mut v_x_2702_: *mut crate::leanh::LeanObject,
    mut v_x_2703_: *mut crate::leanh::LeanObject,
    mut v_inst_2704_: *mut crate::leanh::LeanObject,
    mut v_inst_2705_: *mut crate::leanh::LeanObject,
    mut v_inst_2706_: *mut crate::leanh::LeanObject,
    mut v_m_2707_: *mut crate::leanh::LeanObject,
    mut v_a_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2709_ = l_Std_ExtDHashMap_getKey_x21(
        v_00_u03b1_2700_,
        v_00_u03b2_2701_,
        v_x_2702_,
        v_x_2703_,
        v_inst_2704_,
        v_inst_2705_,
        v_inst_2706_,
        v_m_2707_,
        v_a_2708_,
    );
    crate::leanh::lean_dec(v_m_2707_);
    crate::leanh::lean_dec(v_inst_2706_);
    return v_res_2709_;
}
pub unsafe fn l_Std_ExtDHashMap_getKeyD___redArg(
    mut v_x_2710_: *mut crate::leanh::LeanObject,
    mut v_x_2711_: *mut crate::leanh::LeanObject,
    mut v_m_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_fallback_2714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2715_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_2710_,
        v_x_2711_,
        v_m_2712_,
        v_a_2713_,
        v_fallback_2714_,
    );
    return v___x_2715_;
}
pub unsafe fn l_Std_ExtDHashMap_getKeyD___redArg___boxed(
    mut v_x_2716_: *mut crate::leanh::LeanObject,
    mut v_x_2717_: *mut crate::leanh::LeanObject,
    mut v_m_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
    mut v_fallback_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_Std_ExtDHashMap_getKeyD___redArg(
        v_x_2716_,
        v_x_2717_,
        v_m_2718_,
        v_a_2719_,
        v_fallback_2720_,
    );
    crate::leanh::lean_dec(v_fallback_2720_);
    crate::leanh::lean_dec(v_m_2718_);
    return v_res_2721_;
}
pub unsafe fn l_Std_ExtDHashMap_getKeyD(
    mut v_00_u03b1_2722_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2723_: *mut crate::leanh::LeanObject,
    mut v_x_2724_: *mut crate::leanh::LeanObject,
    mut v_x_2725_: *mut crate::leanh::LeanObject,
    mut v_inst_2726_: *mut crate::leanh::LeanObject,
    mut v_inst_2727_: *mut crate::leanh::LeanObject,
    mut v_m_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_fallback_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2731_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_2724_,
        v_x_2725_,
        v_m_2728_,
        v_a_2729_,
        v_fallback_2730_,
    );
    return v___x_2731_;
}
pub unsafe fn l_Std_ExtDHashMap_getKeyD___boxed(
    mut v_00_u03b1_2732_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2733_: *mut crate::leanh::LeanObject,
    mut v_x_2734_: *mut crate::leanh::LeanObject,
    mut v_x_2735_: *mut crate::leanh::LeanObject,
    mut v_inst_2736_: *mut crate::leanh::LeanObject,
    mut v_inst_2737_: *mut crate::leanh::LeanObject,
    mut v_m_2738_: *mut crate::leanh::LeanObject,
    mut v_a_2739_: *mut crate::leanh::LeanObject,
    mut v_fallback_2740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2741_ = l_Std_ExtDHashMap_getKeyD(
        v_00_u03b1_2732_,
        v_00_u03b2_2733_,
        v_x_2734_,
        v_x_2735_,
        v_inst_2736_,
        v_inst_2737_,
        v_m_2738_,
        v_a_2739_,
        v_fallback_2740_,
    );
    crate::leanh::lean_dec(v_fallback_2740_);
    crate::leanh::lean_dec(v_m_2738_);
    return v_res_2741_;
}
pub unsafe fn l_Std_ExtDHashMap_size___redArg(
    mut v_m_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_2743_ = crate::leanh::lean_ctor_get(v_m_2742_, 0);
    crate::leanh::lean_inc(v_size_2743_);
    return v_size_2743_;
}
pub unsafe fn l_Std_ExtDHashMap_size___redArg___boxed(
    mut v_m_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2745_ = l_Std_ExtDHashMap_size___redArg(v_m_2744_);
    crate::leanh::lean_dec(v_m_2744_);
    return v_res_2745_;
}
pub unsafe fn l_Std_ExtDHashMap_size(
    mut v_00_u03b1_2746_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2747_: *mut crate::leanh::LeanObject,
    mut v_x_2748_: *mut crate::leanh::LeanObject,
    mut v_x_2749_: *mut crate::leanh::LeanObject,
    mut v_inst_2750_: *mut crate::leanh::LeanObject,
    mut v_inst_2751_: *mut crate::leanh::LeanObject,
    mut v_m_2752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_2753_ = crate::leanh::lean_ctor_get(v_m_2752_, 0);
    crate::leanh::lean_inc(v_size_2753_);
    return v_size_2753_;
}
pub unsafe fn l_Std_ExtDHashMap_size___boxed(
    mut v_00_u03b1_2754_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2755_: *mut crate::leanh::LeanObject,
    mut v_x_2756_: *mut crate::leanh::LeanObject,
    mut v_x_2757_: *mut crate::leanh::LeanObject,
    mut v_inst_2758_: *mut crate::leanh::LeanObject,
    mut v_inst_2759_: *mut crate::leanh::LeanObject,
    mut v_m_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_Std_ExtDHashMap_size(
        v_00_u03b1_2754_,
        v_00_u03b2_2755_,
        v_x_2756_,
        v_x_2757_,
        v_inst_2758_,
        v_inst_2759_,
        v_m_2760_,
    );
    crate::leanh::lean_dec(v_m_2760_);
    crate::leanh::lean_dec_ref(v_x_2757_);
    crate::leanh::lean_dec_ref(v_x_2756_);
    return v_res_2761_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___redArg(
    mut v_m_2762_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    v_size_2763_ = crate::leanh::lean_ctor_get(v_m_2762_, 0);
    v___x_2764_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2765_ = lean_nat_dec_eq(v_size_2763_, v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___redArg___boxed(
    mut v_m_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2767_: u8 = 0;
    let mut v_r_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Std_ExtDHashMap_isEmpty___redArg(v_m_2766_);
    crate::leanh::lean_dec(v_m_2766_);
    v_r_2768_ = crate::leanh::lean_box((v_res_2767_) as usize);
    return v_r_2768_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty(
    mut v_00_u03b1_2769_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2770_: *mut crate::leanh::LeanObject,
    mut v_x_2771_: *mut crate::leanh::LeanObject,
    mut v_x_2772_: *mut crate::leanh::LeanObject,
    mut v_inst_2773_: *mut crate::leanh::LeanObject,
    mut v_inst_2774_: *mut crate::leanh::LeanObject,
    mut v_m_2775_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    v_size_2776_ = crate::leanh::lean_ctor_get(v_m_2775_, 0);
    v___x_2777_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2778_ = lean_nat_dec_eq(v_size_2776_, v___x_2777_);
    return v___x_2778_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___boxed(
    mut v_00_u03b1_2779_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2780_: *mut crate::leanh::LeanObject,
    mut v_x_2781_: *mut crate::leanh::LeanObject,
    mut v_x_2782_: *mut crate::leanh::LeanObject,
    mut v_inst_2783_: *mut crate::leanh::LeanObject,
    mut v_inst_2784_: *mut crate::leanh::LeanObject,
    mut v_m_2785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2786_: u8 = 0;
    let mut v_r_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2786_ = l_Std_ExtDHashMap_isEmpty(
        v_00_u03b1_2779_,
        v_00_u03b2_2780_,
        v_x_2781_,
        v_x_2782_,
        v_inst_2783_,
        v_inst_2784_,
        v_m_2785_,
    );
    crate::leanh::lean_dec(v_m_2785_);
    crate::leanh::lean_dec_ref(v_x_2782_);
    crate::leanh::lean_dec_ref(v_x_2781_);
    v_r_2787_ = crate::leanh::lean_box((v_res_2786_) as usize);
    return v_r_2787_;
}
pub unsafe fn l_Std_ExtDHashMap_filter___redArg(
    mut v_f_2788_: *mut crate::leanh::LeanObject,
    mut v_m_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2790_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2788_, v_m_2789_);
    return v___x_2790_;
}
pub unsafe fn l_Std_ExtDHashMap_filter(
    mut v_00_u03b1_2791_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2792_: *mut crate::leanh::LeanObject,
    mut v_x_2793_: *mut crate::leanh::LeanObject,
    mut v_x_2794_: *mut crate::leanh::LeanObject,
    mut v_inst_2795_: *mut crate::leanh::LeanObject,
    mut v_inst_2796_: *mut crate::leanh::LeanObject,
    mut v_f_2797_: *mut crate::leanh::LeanObject,
    mut v_m_2798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2799_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2797_, v_m_2798_);
    return v___x_2799_;
}
pub unsafe fn l_Std_ExtDHashMap_filter___boxed(
    mut v_00_u03b1_2800_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2801_: *mut crate::leanh::LeanObject,
    mut v_x_2802_: *mut crate::leanh::LeanObject,
    mut v_x_2803_: *mut crate::leanh::LeanObject,
    mut v_inst_2804_: *mut crate::leanh::LeanObject,
    mut v_inst_2805_: *mut crate::leanh::LeanObject,
    mut v_f_2806_: *mut crate::leanh::LeanObject,
    mut v_m_2807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2808_ = l_Std_ExtDHashMap_filter(
        v_00_u03b1_2800_,
        v_00_u03b2_2801_,
        v_x_2802_,
        v_x_2803_,
        v_inst_2804_,
        v_inst_2805_,
        v_f_2806_,
        v_m_2807_,
    );
    crate::leanh::lean_dec_ref(v_x_2803_);
    crate::leanh::lean_dec_ref(v_x_2802_);
    return v_res_2808_;
}
pub unsafe fn l_Std_ExtDHashMap_map___redArg(
    mut v_f_2809_: *mut crate::leanh::LeanObject,
    mut v_m_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2811_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2809_, v_m_2810_);
    return v___x_2811_;
}
pub unsafe fn l_Std_ExtDHashMap_map(
    mut v_00_u03b1_2812_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2813_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2814_: *mut crate::leanh::LeanObject,
    mut v_x_2815_: *mut crate::leanh::LeanObject,
    mut v_x_2816_: *mut crate::leanh::LeanObject,
    mut v_inst_2817_: *mut crate::leanh::LeanObject,
    mut v_inst_2818_: *mut crate::leanh::LeanObject,
    mut v_f_2819_: *mut crate::leanh::LeanObject,
    mut v_m_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2821_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2819_, v_m_2820_);
    return v___x_2821_;
}
pub unsafe fn l_Std_ExtDHashMap_map___boxed(
    mut v_00_u03b1_2822_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2823_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2824_: *mut crate::leanh::LeanObject,
    mut v_x_2825_: *mut crate::leanh::LeanObject,
    mut v_x_2826_: *mut crate::leanh::LeanObject,
    mut v_inst_2827_: *mut crate::leanh::LeanObject,
    mut v_inst_2828_: *mut crate::leanh::LeanObject,
    mut v_f_2829_: *mut crate::leanh::LeanObject,
    mut v_m_2830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2831_ = l_Std_ExtDHashMap_map(
        v_00_u03b1_2822_,
        v_00_u03b2_2823_,
        v_00_u03b3_2824_,
        v_x_2825_,
        v_x_2826_,
        v_inst_2827_,
        v_inst_2828_,
        v_f_2829_,
        v_m_2830_,
    );
    crate::leanh::lean_dec_ref(v_x_2826_);
    crate::leanh::lean_dec_ref(v_x_2825_);
    return v_res_2831_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap___redArg(
    mut v_f_2832_: *mut crate::leanh::LeanObject,
    mut v_m_2833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2834_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2832_, v_m_2833_);
    return v___x_2834_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap(
    mut v_00_u03b1_2835_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2836_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2837_: *mut crate::leanh::LeanObject,
    mut v_x_2838_: *mut crate::leanh::LeanObject,
    mut v_x_2839_: *mut crate::leanh::LeanObject,
    mut v_inst_2840_: *mut crate::leanh::LeanObject,
    mut v_inst_2841_: *mut crate::leanh::LeanObject,
    mut v_f_2842_: *mut crate::leanh::LeanObject,
    mut v_m_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2842_, v_m_2843_);
    return v___x_2844_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap___boxed(
    mut v_00_u03b1_2845_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2846_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2847_: *mut crate::leanh::LeanObject,
    mut v_x_2848_: *mut crate::leanh::LeanObject,
    mut v_x_2849_: *mut crate::leanh::LeanObject,
    mut v_inst_2850_: *mut crate::leanh::LeanObject,
    mut v_inst_2851_: *mut crate::leanh::LeanObject,
    mut v_f_2852_: *mut crate::leanh::LeanObject,
    mut v_m_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2854_ = l_Std_ExtDHashMap_filterMap(
        v_00_u03b1_2845_,
        v_00_u03b2_2846_,
        v_00_u03b3_2847_,
        v_x_2848_,
        v_x_2849_,
        v_inst_2850_,
        v_inst_2851_,
        v_f_2852_,
        v_m_2853_,
    );
    crate::leanh::lean_dec_ref(v_x_2849_);
    crate::leanh::lean_dec_ref(v_x_2848_);
    return v_res_2854_;
}
pub unsafe fn l_Std_ExtDHashMap_modify___redArg(
    mut v_x_2855_: *mut crate::leanh::LeanObject,
    mut v_x_2856_: *mut crate::leanh::LeanObject,
    mut v_m_2857_: *mut crate::leanh::LeanObject,
    mut v_a_2858_: *mut crate::leanh::LeanObject,
    mut v_f_2859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_x_2855_, v_x_2856_, v_m_2857_, v_a_2858_, v_f_2859_,
    );
    return v___x_2860_;
}
pub unsafe fn l_Std_ExtDHashMap_modify(
    mut v_00_u03b1_2861_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2862_: *mut crate::leanh::LeanObject,
    mut v_x_2863_: *mut crate::leanh::LeanObject,
    mut v_x_2864_: *mut crate::leanh::LeanObject,
    mut v_inst_2865_: *mut crate::leanh::LeanObject,
    mut v_m_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
    mut v_f_2868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_x_2863_, v_x_2864_, v_m_2866_, v_a_2867_, v_f_2868_,
    );
    return v___x_2869_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_modify___redArg(
    mut v_x_2870_: *mut crate::leanh::LeanObject,
    mut v_x_2871_: *mut crate::leanh::LeanObject,
    mut v_m_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_f_2874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_2870_, v_x_2871_, v_m_2872_, v_a_2873_, v_f_2874_,
    );
    return v___x_2875_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_modify(
    mut v_00_u03b1_2876_: *mut crate::leanh::LeanObject,
    mut v_x_2877_: *mut crate::leanh::LeanObject,
    mut v_x_2878_: *mut crate::leanh::LeanObject,
    mut v_inst_2879_: *mut crate::leanh::LeanObject,
    mut v_inst_2880_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2881_: *mut crate::leanh::LeanObject,
    mut v_m_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
    mut v_f_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_2877_, v_x_2878_, v_m_2882_, v_a_2883_, v_f_2884_,
    );
    return v___x_2885_;
}
pub unsafe fn l_Std_ExtDHashMap_alter___redArg(
    mut v_x_2886_: *mut crate::leanh::LeanObject,
    mut v_x_2887_: *mut crate::leanh::LeanObject,
    mut v_m_2888_: *mut crate::leanh::LeanObject,
    mut v_a_2889_: *mut crate::leanh::LeanObject,
    mut v_f_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2891_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_x_2886_, v_x_2887_, v_m_2888_, v_a_2889_, v_f_2890_,
    );
    return v___x_2891_;
}
pub unsafe fn l_Std_ExtDHashMap_alter(
    mut v_00_u03b1_2892_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2893_: *mut crate::leanh::LeanObject,
    mut v_x_2894_: *mut crate::leanh::LeanObject,
    mut v_x_2895_: *mut crate::leanh::LeanObject,
    mut v_inst_2896_: *mut crate::leanh::LeanObject,
    mut v_m_2897_: *mut crate::leanh::LeanObject,
    mut v_a_2898_: *mut crate::leanh::LeanObject,
    mut v_f_2899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2900_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_x_2894_, v_x_2895_, v_m_2897_, v_a_2898_, v_f_2899_,
    );
    return v___x_2900_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_alter___redArg(
    mut v_x_2901_: *mut crate::leanh::LeanObject,
    mut v_x_2902_: *mut crate::leanh::LeanObject,
    mut v_m_2903_: *mut crate::leanh::LeanObject,
    mut v_a_2904_: *mut crate::leanh::LeanObject,
    mut v_f_2905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2906_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_2901_, v_x_2902_, v_m_2903_, v_a_2904_, v_f_2905_,
    );
    return v___x_2906_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_alter(
    mut v_00_u03b1_2907_: *mut crate::leanh::LeanObject,
    mut v_x_2908_: *mut crate::leanh::LeanObject,
    mut v_x_2909_: *mut crate::leanh::LeanObject,
    mut v_inst_2910_: *mut crate::leanh::LeanObject,
    mut v_inst_2911_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2912_: *mut crate::leanh::LeanObject,
    mut v_m_2913_: *mut crate::leanh::LeanObject,
    mut v_a_2914_: *mut crate::leanh::LeanObject,
    mut v_f_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_2908_, v_x_2909_, v_m_2913_, v_a_2914_, v_f_2915_,
    );
    return v___x_2916_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany___redArg___lam__0(
    mut v_x_2917_: *mut crate::leanh::LeanObject,
    mut v_x_2918_: *mut crate::leanh::LeanObject,
    mut v_x_2919_: *mut crate::leanh::LeanObject,
    mut v_____s_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2921_ = crate::leanh::lean_ctor_get(v_x_2919_, 0);
    crate::leanh::lean_inc(v_fst_2921_);
    v_snd_2922_ = crate::leanh::lean_ctor_get(v_x_2919_, 1);
    crate::leanh::lean_inc(v_snd_2922_);
    crate::leanh::lean_dec_ref(v_x_2919_);
    v_m_2923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2917_,
        v_x_2918_,
        v_____s_2920_,
        v_fst_2921_,
        v_snd_2922_,
    );
    v___x_2924_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2924_, 0, v_m_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany___redArg(
    mut v_x_2925_: *mut crate::leanh::LeanObject,
    mut v_x_2926_: *mut crate::leanh::LeanObject,
    mut v_inst_2927_: *mut crate::leanh::LeanObject,
    mut v_m_2928_: *mut crate::leanh::LeanObject,
    mut v_l_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2930_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2930_, 0, v_x_2925_);
    crate::leanh::lean_closure_set(v___f_2930_, 1, v_x_2926_);
    v___x_2931_ = crate::leanh::lean_apply_4(
        v_inst_2927_,
        crate::leanh::lean_box(0),
        v_l_2929_,
        v_m_2928_,
        v___f_2930_,
    );
    return v___x_2931_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany(
    mut v_00_u03b1_2932_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2933_: *mut crate::leanh::LeanObject,
    mut v_x_2934_: *mut crate::leanh::LeanObject,
    mut v_x_2935_: *mut crate::leanh::LeanObject,
    mut v_inst_2936_: *mut crate::leanh::LeanObject,
    mut v_inst_2937_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_2938_: *mut crate::leanh::LeanObject,
    mut v_inst_2939_: *mut crate::leanh::LeanObject,
    mut v_m_2940_: *mut crate::leanh::LeanObject,
    mut v_l_2941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2942_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2942_, 0, v_x_2934_);
    crate::leanh::lean_closure_set(v___f_2942_, 1, v_x_2935_);
    v___x_2943_ = crate::leanh::lean_apply_4(
        v_inst_2939_,
        crate::leanh::lean_box(0),
        v_l_2941_,
        v_m_2940_,
        v___f_2942_,
    );
    return v___x_2943_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0(
    mut v_x_2944_: *mut crate::leanh::LeanObject,
    mut v_x_2945_: *mut crate::leanh::LeanObject,
    mut v_x_2946_: *mut crate::leanh::LeanObject,
    mut v_____s_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2948_ = crate::leanh::lean_ctor_get(v_x_2946_, 0);
    crate::leanh::lean_inc(v_fst_2948_);
    v_snd_2949_ = crate::leanh::lean_ctor_get(v_x_2946_, 1);
    crate::leanh::lean_inc(v_snd_2949_);
    crate::leanh::lean_dec_ref(v_x_2946_);
    v_m_2950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2944_,
        v_x_2945_,
        v_____s_2947_,
        v_fst_2948_,
        v_snd_2949_,
    );
    v___x_2951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2951_, 0, v_m_2950_);
    return v___x_2951_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany___redArg(
    mut v_x_2952_: *mut crate::leanh::LeanObject,
    mut v_x_2953_: *mut crate::leanh::LeanObject,
    mut v_inst_2954_: *mut crate::leanh::LeanObject,
    mut v_m_2955_: *mut crate::leanh::LeanObject,
    mut v_l_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2957_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2957_, 0, v_x_2952_);
    crate::leanh::lean_closure_set(v___f_2957_, 1, v_x_2953_);
    v___x_2958_ = crate::leanh::lean_apply_4(
        v_inst_2954_,
        crate::leanh::lean_box(0),
        v_l_2956_,
        v_m_2955_,
        v___f_2957_,
    );
    return v___x_2958_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany(
    mut v_00_u03b1_2959_: *mut crate::leanh::LeanObject,
    mut v_x_2960_: *mut crate::leanh::LeanObject,
    mut v_x_2961_: *mut crate::leanh::LeanObject,
    mut v_inst_2962_: *mut crate::leanh::LeanObject,
    mut v_inst_2963_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2964_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_2965_: *mut crate::leanh::LeanObject,
    mut v_inst_2966_: *mut crate::leanh::LeanObject,
    mut v_m_2967_: *mut crate::leanh::LeanObject,
    mut v_l_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2969_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2969_, 0, v_x_2960_);
    crate::leanh::lean_closure_set(v___f_2969_, 1, v_x_2961_);
    v___x_2970_ = crate::leanh::lean_apply_4(
        v_inst_2966_,
        crate::leanh::lean_box(0),
        v_l_2968_,
        v_m_2967_,
        v___f_2969_,
    );
    return v___x_2970_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0(
    mut v_x_2971_: *mut crate::leanh::LeanObject,
    mut v_x_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_____s_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = crate::leanh::lean_box(0);
    v_m_2976_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2971_,
        v_x_2972_,
        v_____s_2974_,
        v_a_2973_,
        v___x_2975_,
    );
    v___x_2977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2977_, 0, v_m_2976_);
    return v___x_2977_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg(
    mut v_x_2978_: *mut crate::leanh::LeanObject,
    mut v_x_2979_: *mut crate::leanh::LeanObject,
    mut v_inst_2980_: *mut crate::leanh::LeanObject,
    mut v_m_2981_: *mut crate::leanh::LeanObject,
    mut v_l_2982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2983_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2983_, 0, v_x_2978_);
    crate::leanh::lean_closure_set(v___f_2983_, 1, v_x_2979_);
    v___x_2984_ = crate::leanh::lean_apply_4(
        v_inst_2980_,
        crate::leanh::lean_box(0),
        v_l_2982_,
        v_m_2981_,
        v___f_2983_,
    );
    return v___x_2984_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit(
    mut v_00_u03b1_2985_: *mut crate::leanh::LeanObject,
    mut v_x_2986_: *mut crate::leanh::LeanObject,
    mut v_x_2987_: *mut crate::leanh::LeanObject,
    mut v_inst_2988_: *mut crate::leanh::LeanObject,
    mut v_inst_2989_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_2990_: *mut crate::leanh::LeanObject,
    mut v_inst_2991_: *mut crate::leanh::LeanObject,
    mut v_m_2992_: *mut crate::leanh::LeanObject,
    mut v_l_2993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2994_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2994_, 0, v_x_2986_);
    crate::leanh::lean_closure_set(v___f_2994_, 1, v_x_2987_);
    v___x_2995_ = crate::leanh::lean_apply_4(
        v_inst_2991_,
        crate::leanh::lean_box(0),
        v_l_2993_,
        v_m_2992_,
        v___f_2994_,
    );
    return v___x_2995_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg___lam__0(
    mut v_x_2996_: *mut crate::leanh::LeanObject,
    mut v_x_2997_: *mut crate::leanh::LeanObject,
    mut v_a_2998_: *mut crate::leanh::LeanObject,
    mut v_b_2999_: *mut crate::leanh::LeanObject,
    mut v_acc_3000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_3001_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2996_,
        v_x_2997_,
        v_acc_3000_,
        v_a_2998_,
        v_b_2999_,
    );
    v___x_3002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3002_, 0, v_r_3001_);
    return v___x_3002_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg___lam__1(
    mut v___x_3003_: *mut crate::leanh::LeanObject,
    mut v___f_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
    mut v_x_3006_: *mut crate::leanh::LeanObject,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_3003_, v___f_3004_, v_a_3005_, v___y_3007_);
    return v___x_3008_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg(
    mut v_x_3030_: *mut crate::leanh::LeanObject,
    mut v_x_3031_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3032_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: u8 = 0;
    v_size_3034_ = crate::leanh::lean_ctor_get(v_m_u2081_3032_, 0);
    v_buckets_3035_ = crate::leanh::lean_ctor_get(v_m_u2081_3032_, 1);
    v_size_3036_ = crate::leanh::lean_ctor_get(v_m_u2082_3033_, 0);
    v___x_3037_ = lean_nat_dec_le(v_size_3034_, v_size_3036_);
    if v___x_3037_ == 0 {
        let mut v___f_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_3038_ = l_Std_ExtDHashMap_union___redArg___closed__10;
        v___x_3039_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_3038_,
            v_x_3030_,
            v_x_3031_,
            v_m_u2081_3032_,
            v_m_u2082_3033_,
        );
        return v___x_3039_;
    } else {
        let mut v___f_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3043_: usize = 0;
        let mut v___x_3044_: usize = 0;
        let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_3035_);
        crate::leanh::lean_dec(v_m_u2081_3032_);
        v___f_3040_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3040_, 0, v_x_3030_);
        crate::leanh::lean_closure_set(v___f_3040_, 1, v_x_3031_);
        v___x_3041_ = l_Std_ExtDHashMap_union___redArg___closed__9;
        v___f_3042_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3042_, 0, v___x_3041_);
        crate::leanh::lean_closure_set(v___f_3042_, 1, v___f_3040_);
        v_sz_3043_ = lean_array_size(v_buckets_3035_);
        v___x_3044_ = 0usize;
        v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3041_,
            v_buckets_3035_,
            v___f_3042_,
            v_sz_3043_,
            v___x_3044_,
            v_m_u2082_3033_,
        );
        return v___x_3045_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_union(
    mut v_00_u03b1_3046_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3047_: *mut crate::leanh::LeanObject,
    mut v_x_3048_: *mut crate::leanh::LeanObject,
    mut v_x_3049_: *mut crate::leanh::LeanObject,
    mut v_inst_3050_: *mut crate::leanh::LeanObject,
    mut v_inst_3051_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3052_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    v_size_3054_ = crate::leanh::lean_ctor_get(v_m_u2081_3052_, 0);
    v_buckets_3055_ = crate::leanh::lean_ctor_get(v_m_u2081_3052_, 1);
    v_size_3056_ = crate::leanh::lean_ctor_get(v_m_u2082_3053_, 0);
    v___x_3057_ = lean_nat_dec_le(v_size_3054_, v_size_3056_);
    if v___x_3057_ == 0 {
        let mut v___f_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_3058_ = l_Std_ExtDHashMap_union___redArg___closed__10;
        v___x_3059_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_3058_,
            v_x_3048_,
            v_x_3049_,
            v_m_u2081_3052_,
            v_m_u2082_3053_,
        );
        return v___x_3059_;
    } else {
        let mut v___f_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3063_: usize = 0;
        let mut v___x_3064_: usize = 0;
        let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_3055_);
        crate::leanh::lean_dec(v_m_u2081_3052_);
        v___f_3060_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3060_, 0, v_x_3048_);
        crate::leanh::lean_closure_set(v___f_3060_, 1, v_x_3049_);
        v___x_3061_ = l_Std_ExtDHashMap_union___redArg___closed__9;
        v___f_3062_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3062_, 0, v___x_3061_);
        crate::leanh::lean_closure_set(v___f_3062_, 1, v___f_3060_);
        v_sz_3063_ = lean_array_size(v_buckets_3055_);
        v___x_3064_ = 0usize;
        v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3061_,
            v_buckets_3055_,
            v___f_3062_,
            v_sz_3063_,
            v___x_3064_,
            v_m_u2082_3053_,
        );
        return v___x_3065_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_3066_: *mut crate::leanh::LeanObject,
    mut v_x_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtDHashMap_union as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_3068_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3068_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3068_, 2, v_x_3066_);
    crate::leanh::lean_closure_set(v___x_3068_, 3, v_x_3067_);
    crate::leanh::lean_closure_set(v___x_3068_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3068_, 5, crate::leanh::lean_box(0));
    return v___x_3068_;
}
pub unsafe fn l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3069_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3070_: *mut crate::leanh::LeanObject,
    mut v_x_3071_: *mut crate::leanh::LeanObject,
    mut v_x_3072_: *mut crate::leanh::LeanObject,
    mut v_inst_3073_: *mut crate::leanh::LeanObject,
    mut v_inst_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3075_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtDHashMap_union as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_3075_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3075_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3075_, 2, v_x_3071_);
    crate::leanh::lean_closure_set(v___x_3075_, 3, v_x_3072_);
    crate::leanh::lean_closure_set(v___x_3075_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3075_, 5, crate::leanh::lean_box(0));
    return v___x_3075_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(
    mut v_x_3076_: *mut crate::leanh::LeanObject,
    mut v_x_3077_: *mut crate::leanh::LeanObject,
    mut v_inst_3078_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3079_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3080_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3081_: u8 = 0;
    v___x_3081_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_x_3076_,
        v_x_3077_,
        v_inst_3078_,
        v_m_u2081_3079_,
        v_m_u2082_3080_,
    );
    return v___x_3081_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed(
    mut v_x_3082_: *mut crate::leanh::LeanObject,
    mut v_x_3083_: *mut crate::leanh::LeanObject,
    mut v_inst_3084_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3085_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3087_: u8 = 0;
    let mut v_r_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(
        v_x_3082_,
        v_x_3083_,
        v_inst_3084_,
        v_m_u2081_3085_,
        v_m_u2082_3086_,
    );
    v_r_3088_ = crate::leanh::lean_box((v_res_3087_) as usize);
    return v_r_3088_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg(
    mut v_x_3089_: *mut crate::leanh::LeanObject,
    mut v_x_3090_: *mut crate::leanh::LeanObject,
    mut v_inst_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3092_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3092_, 0, v_x_3089_);
    crate::leanh::lean_closure_set(v___f_3092_, 1, v_x_3090_);
    crate::leanh::lean_closure_set(v___f_3092_, 2, v_inst_3091_);
    return v___f_3092_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq(
    mut v_00_u03b1_3093_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3094_: *mut crate::leanh::LeanObject,
    mut v_x_3095_: *mut crate::leanh::LeanObject,
    mut v_x_3096_: *mut crate::leanh::LeanObject,
    mut v_inst_3097_: *mut crate::leanh::LeanObject,
    mut v_inst_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3099_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3099_, 0, v_x_3095_);
    crate::leanh::lean_closure_set(v___f_3099_, 1, v_x_3096_);
    crate::leanh::lean_closure_set(v___f_3099_, 2, v_inst_3098_);
    return v___f_3099_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(
    mut v_inst_3100_: *mut crate::leanh::LeanObject,
    mut v_inst_3101_: *mut crate::leanh::LeanObject,
    mut v_inst_3102_: *mut crate::leanh::LeanObject,
    mut v_x_3103_: *mut crate::leanh::LeanObject,
    mut v_x_3104_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3105_: u8 = 0;
    v___x_3105_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_3100_,
        v_inst_3101_,
        v_inst_3102_,
        v_x_3103_,
        v_x_3104_,
    );
    return v___x_3105_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(
    mut v_inst_3106_: *mut crate::leanh::LeanObject,
    mut v_inst_3107_: *mut crate::leanh::LeanObject,
    mut v_inst_3108_: *mut crate::leanh::LeanObject,
    mut v_x_3109_: *mut crate::leanh::LeanObject,
    mut v_x_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3111_: u8 = 0;
    let mut v_r_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3111_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(
        v_inst_3106_,
        v_inst_3107_,
        v_inst_3108_,
        v_x_3109_,
        v_x_3110_,
    );
    v_r_3112_ = crate::leanh::lean_box((v_res_3111_) as usize);
    return v_r_3112_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(
    mut v_00_u03b1_3113_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3114_: *mut crate::leanh::LeanObject,
    mut v_inst_3115_: *mut crate::leanh::LeanObject,
    mut v_inst_3116_: *mut crate::leanh::LeanObject,
    mut v_inst_3117_: *mut crate::leanh::LeanObject,
    mut v_inst_3118_: *mut crate::leanh::LeanObject,
    mut v_inst_3119_: *mut crate::leanh::LeanObject,
    mut v_x_3120_: *mut crate::leanh::LeanObject,
    mut v_x_3121_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3122_: u8 = 0;
    v___x_3122_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_3115_,
        v_inst_3117_,
        v_inst_3118_,
        v_x_3120_,
        v_x_3121_,
    );
    return v___x_3122_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___boxed(
    mut v_00_u03b1_3123_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3124_: *mut crate::leanh::LeanObject,
    mut v_inst_3125_: *mut crate::leanh::LeanObject,
    mut v_inst_3126_: *mut crate::leanh::LeanObject,
    mut v_inst_3127_: *mut crate::leanh::LeanObject,
    mut v_inst_3128_: *mut crate::leanh::LeanObject,
    mut v_inst_3129_: *mut crate::leanh::LeanObject,
    mut v_x_3130_: *mut crate::leanh::LeanObject,
    mut v_x_3131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3132_: u8 = 0;
    let mut v_r_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3132_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(
        v_00_u03b1_3123_,
        v_00_u03b2_3124_,
        v_inst_3125_,
        v_inst_3126_,
        v_inst_3127_,
        v_inst_3128_,
        v_inst_3129_,
        v_x_3130_,
        v_x_3131_,
    );
    v_r_3133_ = crate::leanh::lean_box((v_res_3132_) as usize);
    return v_r_3133_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_beq___redArg(
    mut v_x_3134_: *mut crate::leanh::LeanObject,
    mut v_x_3135_: *mut crate::leanh::LeanObject,
    mut v_inst_3136_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3137_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3138_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3139_: u8 = 0;
    v___x_3139_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_x_3134_,
        v_x_3135_,
        v_inst_3136_,
        v_m_u2081_3137_,
        v_m_u2082_3138_,
    );
    return v___x_3139_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_beq___redArg___boxed(
    mut v_x_3140_: *mut crate::leanh::LeanObject,
    mut v_x_3141_: *mut crate::leanh::LeanObject,
    mut v_inst_3142_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3143_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3145_: u8 = 0;
    let mut v_r_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Std_ExtDHashMap_Const_beq___redArg(
        v_x_3140_,
        v_x_3141_,
        v_inst_3142_,
        v_m_u2081_3143_,
        v_m_u2082_3144_,
    );
    v_r_3146_ = crate::leanh::lean_box((v_res_3145_) as usize);
    return v_r_3146_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_beq(
    mut v_00_u03b1_3147_: *mut crate::leanh::LeanObject,
    mut v_x_3148_: *mut crate::leanh::LeanObject,
    mut v_x_3149_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3150_: *mut crate::leanh::LeanObject,
    mut v_inst_3151_: *mut crate::leanh::LeanObject,
    mut v_inst_3152_: *mut crate::leanh::LeanObject,
    mut v_inst_3153_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3154_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3155_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3156_: u8 = 0;
    v___x_3156_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_x_3148_,
        v_x_3149_,
        v_inst_3153_,
        v_m_u2081_3154_,
        v_m_u2082_3155_,
    );
    return v___x_3156_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_beq___boxed(
    mut v_00_u03b1_3157_: *mut crate::leanh::LeanObject,
    mut v_x_3158_: *mut crate::leanh::LeanObject,
    mut v_x_3159_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3160_: *mut crate::leanh::LeanObject,
    mut v_inst_3161_: *mut crate::leanh::LeanObject,
    mut v_inst_3162_: *mut crate::leanh::LeanObject,
    mut v_inst_3163_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3164_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3166_: u8 = 0;
    let mut v_r_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3166_ = l_Std_ExtDHashMap_Const_beq(
        v_00_u03b1_3157_,
        v_x_3158_,
        v_x_3159_,
        v_00_u03b2_3160_,
        v_inst_3161_,
        v_inst_3162_,
        v_inst_3163_,
        v_m_u2081_3164_,
        v_m_u2082_3165_,
    );
    v_r_3167_ = crate::leanh::lean_box((v_res_3166_) as usize);
    return v_r_3167_;
}
pub unsafe fn l_Std_ExtDHashMap_inter___redArg(
    mut v_x_3168_: *mut crate::leanh::LeanObject,
    mut v_x_3169_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3170_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3172_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_3168_,
        v_x_3169_,
        v_m_u2081_3170_,
        v_m_u2082_3171_,
    );
    return v___x_3172_;
}
pub unsafe fn l_Std_ExtDHashMap_inter(
    mut v_00_u03b1_3173_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3174_: *mut crate::leanh::LeanObject,
    mut v_x_3175_: *mut crate::leanh::LeanObject,
    mut v_x_3176_: *mut crate::leanh::LeanObject,
    mut v_inst_3177_: *mut crate::leanh::LeanObject,
    mut v_inst_3178_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3179_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3181_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_3175_,
        v_x_3176_,
        v_m_u2081_3179_,
        v_m_u2082_3180_,
    );
    return v___x_3181_;
}
pub unsafe fn l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_3182_: *mut crate::leanh::LeanObject,
    mut v_x_3183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3184_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtDHashMap_inter as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_3184_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3184_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3184_, 2, v_x_3182_);
    crate::leanh::lean_closure_set(v___x_3184_, 3, v_x_3183_);
    crate::leanh::lean_closure_set(v___x_3184_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3184_, 5, crate::leanh::lean_box(0));
    return v___x_3184_;
}
pub unsafe fn l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3185_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3186_: *mut crate::leanh::LeanObject,
    mut v_x_3187_: *mut crate::leanh::LeanObject,
    mut v_x_3188_: *mut crate::leanh::LeanObject,
    mut v_inst_3189_: *mut crate::leanh::LeanObject,
    mut v_inst_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtDHashMap_inter as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_3191_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3191_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3191_, 2, v_x_3187_);
    crate::leanh::lean_closure_set(v___x_3191_, 3, v_x_3188_);
    crate::leanh::lean_closure_set(v___x_3191_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3191_, 5, crate::leanh::lean_box(0));
    return v___x_3191_;
}
pub unsafe fn l_Std_ExtDHashMap_diff___redArg___lam__0(
    mut v_x_3192_: *mut crate::leanh::LeanObject,
    mut v_x_3193_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3194_: *mut crate::leanh::LeanObject,
    mut v___x_3195_: u8,
    mut v_k_3196_: *mut crate::leanh::LeanObject,
    mut v_x_3197_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3198_: u8 = 0;
    v___x_3198_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_3192_,
        v_x_3193_,
        v_m_u2082_3194_,
        v_k_3196_,
    );
    if v___x_3198_ == 0 {
        return v___x_3195_;
    } else {
        let mut v___x_3199_: u8 = 0;
        v___x_3199_ = 0;
        return v___x_3199_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_diff___redArg___lam__0___boxed(
    mut v_x_3200_: *mut crate::leanh::LeanObject,
    mut v_x_3201_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3202_: *mut crate::leanh::LeanObject,
    mut v___x_3203_: *mut crate::leanh::LeanObject,
    mut v_k_3204_: *mut crate::leanh::LeanObject,
    mut v_x_3205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_108__boxed_3206_: u8 = 0;
    let mut v_res_3207_: u8 = 0;
    let mut v_r_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_108__boxed_3206_ = (crate::leanh::lean_unbox(v___x_3203_) as u8);
    v_res_3207_ = l_Std_ExtDHashMap_diff___redArg___lam__0(
        v_x_3200_,
        v_x_3201_,
        v_m_u2082_3202_,
        v___x_108__boxed_3206_,
        v_k_3204_,
        v_x_3205_,
    );
    crate::leanh::lean_dec(v_x_3205_);
    crate::leanh::lean_dec(v_m_u2082_3202_);
    v_r_3208_ = crate::leanh::lean_box((v_res_3207_) as usize);
    return v_r_3208_;
}
pub unsafe fn l_Std_ExtDHashMap_diff___redArg(
    mut v_x_3209_: *mut crate::leanh::LeanObject,
    mut v_x_3210_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3211_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    v_size_3213_ = crate::leanh::lean_ctor_get(v_m_u2081_3211_, 0);
    v_size_3214_ = crate::leanh::lean_ctor_get(v_m_u2082_3212_, 0);
    v___x_3215_ = lean_nat_dec_le(v_size_3213_, v_size_3214_);
    if v___x_3215_ == 0 {
        let mut v___f_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_3216_ = l_Std_ExtDHashMap_union___redArg___closed__10;
        v___x_3217_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_3216_,
            v_x_3209_,
            v_x_3210_,
            v_m_u2081_3211_,
            v_m_u2082_3212_,
        );
        return v___x_3217_;
    } else {
        let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3218_ = crate::leanh::lean_box((v___x_3215_) as usize);
        v___f_3219_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_3219_, 0, v_x_3209_);
        crate::leanh::lean_closure_set(v___f_3219_, 1, v_x_3210_);
        crate::leanh::lean_closure_set(v___f_3219_, 2, v_m_u2082_3212_);
        crate::leanh::lean_closure_set(v___f_3219_, 3, v___x_3218_);
        v___x_3220_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3219_, v_m_u2081_3211_);
        return v___x_3220_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_diff(
    mut v_00_u03b1_3221_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3222_: *mut crate::leanh::LeanObject,
    mut v_x_3223_: *mut crate::leanh::LeanObject,
    mut v_x_3224_: *mut crate::leanh::LeanObject,
    mut v_inst_3225_: *mut crate::leanh::LeanObject,
    mut v_inst_3226_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3227_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    v_size_3229_ = crate::leanh::lean_ctor_get(v_m_u2081_3227_, 0);
    v_size_3230_ = crate::leanh::lean_ctor_get(v_m_u2082_3228_, 0);
    v___x_3231_ = lean_nat_dec_le(v_size_3229_, v_size_3230_);
    if v___x_3231_ == 0 {
        let mut v___f_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_3232_ = l_Std_ExtDHashMap_union___redArg___closed__10;
        v___x_3233_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_3232_,
            v_x_3223_,
            v_x_3224_,
            v_m_u2081_3227_,
            v_m_u2082_3228_,
        );
        return v___x_3233_;
    } else {
        let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3234_ = crate::leanh::lean_box((v___x_3231_) as usize);
        v___f_3235_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_3235_, 0, v_x_3223_);
        crate::leanh::lean_closure_set(v___f_3235_, 1, v_x_3224_);
        crate::leanh::lean_closure_set(v___f_3235_, 2, v_m_u2082_3228_);
        crate::leanh::lean_closure_set(v___f_3235_, 3, v___x_3234_);
        v___x_3236_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3235_, v_m_u2081_3227_);
        return v___x_3236_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_3237_: *mut crate::leanh::LeanObject,
    mut v_x_3238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3239_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtDHashMap_diff as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_3239_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3239_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3239_, 2, v_x_3237_);
    crate::leanh::lean_closure_set(v___x_3239_, 3, v_x_3238_);
    crate::leanh::lean_closure_set(v___x_3239_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3239_, 5, crate::leanh::lean_box(0));
    return v___x_3239_;
}
pub unsafe fn l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3240_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3241_: *mut crate::leanh::LeanObject,
    mut v_x_3242_: *mut crate::leanh::LeanObject,
    mut v_x_3243_: *mut crate::leanh::LeanObject,
    mut v_inst_3244_: *mut crate::leanh::LeanObject,
    mut v_inst_3245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtDHashMap_diff as *mut core::ffi::c_void, 8, 6);
    crate::leanh::lean_closure_set(v___x_3246_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3246_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3246_, 2, v_x_3242_);
    crate::leanh::lean_closure_set(v___x_3246_, 3, v_x_3243_);
    crate::leanh::lean_closure_set(v___x_3246_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3246_, 5, crate::leanh::lean_box(0));
    return v___x_3246_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_unitOfArray___redArg(
    mut v_inst_3251_: *mut crate::leanh::LeanObject,
    mut v_inst_3252_: *mut crate::leanh::LeanObject,
    mut v_l_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3254_ = l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_3255_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_3256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_3254_,
        v_inst_3251_,
        v_inst_3252_,
        v___x_3255_,
        v_l_3253_,
    );
    return v___x_3256_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_unitOfArray(
    mut v_00_u03b1_3257_: *mut crate::leanh::LeanObject,
    mut v_inst_3258_: *mut crate::leanh::LeanObject,
    mut v_inst_3259_: *mut crate::leanh::LeanObject,
    mut v_l_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3261_ = l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_3262_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_3263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_3261_,
        v_inst_3258_,
        v_inst_3259_,
        v___x_3262_,
        v_l_3260_,
    );
    return v___x_3263_;
}
pub unsafe fn l_Std_ExtDHashMap_ofList___redArg(
    mut v_inst_3268_: *mut crate::leanh::LeanObject,
    mut v_inst_3269_: *mut crate::leanh::LeanObject,
    mut v_l_3270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3271_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3272_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_3273_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v___f_3271_,
        v_inst_3268_,
        v_inst_3269_,
        v___x_3272_,
        v_l_3270_,
    );
    return v___x_3273_;
}
pub unsafe fn l_Std_ExtDHashMap_ofList(
    mut v_00_u03b1_3274_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3275_: *mut crate::leanh::LeanObject,
    mut v_inst_3276_: *mut crate::leanh::LeanObject,
    mut v_inst_3277_: *mut crate::leanh::LeanObject,
    mut v_l_3278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3279_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3280_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_3281_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v___f_3279_,
        v_inst_3276_,
        v_inst_3277_,
        v___x_3280_,
        v_l_3278_,
    );
    return v___x_3281_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_ofList___redArg(
    mut v_inst_3282_: *mut crate::leanh::LeanObject,
    mut v_inst_3283_: *mut crate::leanh::LeanObject,
    mut v_l_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3285_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_3287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_3285_,
        v_inst_3282_,
        v_inst_3283_,
        v___x_3286_,
        v_l_3284_,
    );
    return v___x_3287_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_ofList(
    mut v_00_u03b1_3288_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3289_: *mut crate::leanh::LeanObject,
    mut v_inst_3290_: *mut crate::leanh::LeanObject,
    mut v_inst_3291_: *mut crate::leanh::LeanObject,
    mut v_l_3292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3293_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3294_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_3295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_3293_,
        v_inst_3290_,
        v_inst_3291_,
        v___x_3294_,
        v_l_3292_,
    );
    return v___x_3295_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_unitOfList___redArg(
    mut v_inst_3296_: *mut crate::leanh::LeanObject,
    mut v_inst_3297_: *mut crate::leanh::LeanObject,
    mut v_l_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3299_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3300_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_3301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_3299_,
        v_inst_3296_,
        v_inst_3297_,
        v___x_3300_,
        v_l_3298_,
    );
    return v___x_3301_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_unitOfList(
    mut v_00_u03b1_3302_: *mut crate::leanh::LeanObject,
    mut v_inst_3303_: *mut crate::leanh::LeanObject,
    mut v_inst_3304_: *mut crate::leanh::LeanObject,
    mut v_l_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3306_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3307_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    v___x_3308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_3306_,
        v_inst_3303_,
        v_inst_3304_,
        v___x_3307_,
        v_l_3305_,
    );
    return v___x_3308_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ExtDHashMap_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtDHashMap_Basic(
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
pub unsafe fn initialize_Std_Data_ExtDHashMap_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtDHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtDHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_ExtDHashMap_Basic(builtin);
}
