// Lean compiler output
// Module: Std.Data.ExtDHashMap.Basic
// Imports: Std.Data.DHashMap.Lemmas Std.Data.DHashMap.Lemmas
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_div, lean_nat_mul,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
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
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDHashMap_union___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__10_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_ofList___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_ofList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDHashMap_ofList___redArg___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_ofList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_ExtDHashMap_mk___redArg(
    mut v_m_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_m_1655_);
    return v_m_1655_;
}
pub unsafe fn l_Std_ExtDHashMap_mk___redArg___boxed(
    mut v_m_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Std_ExtDHashMap_mk___redArg(v_m_1656_);
    leanh::lean_dec_ref(v_m_1656_);
    return v_res_1657_;
}
pub unsafe fn l_Std_ExtDHashMap_mk(
    mut v_00_u03b1_1658_: *mut leanh::LeanObject,
    mut v_00_u03b2_1659_: *mut leanh::LeanObject,
    mut v_x_1660_: *mut leanh::LeanObject,
    mut v_x_1661_: *mut leanh::LeanObject,
    mut v_m_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_m_1662_);
    return v_m_1662_;
}
pub unsafe fn l_Std_ExtDHashMap_mk___boxed(
    mut v_00_u03b1_1663_: *mut leanh::LeanObject,
    mut v_00_u03b2_1664_: *mut leanh::LeanObject,
    mut v_x_1665_: *mut leanh::LeanObject,
    mut v_x_1666_: *mut leanh::LeanObject,
    mut v_m_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_ExtDHashMap_mk(
        v_00_u03b1_1663_,
        v_00_u03b2_1664_,
        v_x_1665_,
        v_x_1666_,
        v_m_1667_,
    );
    leanh::lean_dec_ref(v_m_1667_);
    leanh::lean_dec_ref(v_x_1666_);
    leanh::lean_dec_ref(v_x_1665_);
    return v_res_1668_;
}
pub unsafe fn l_Std_ExtDHashMap_lift___redArg(
    mut v_f_1669_: *mut leanh::LeanObject,
    mut v_m_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = leanh::lean_apply_1(v_f_1669_, v_m_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Std_ExtDHashMap_lift(
    mut v_00_u03b1_1672_: *mut leanh::LeanObject,
    mut v_00_u03b2_1673_: *mut leanh::LeanObject,
    mut v_x_1674_: *mut leanh::LeanObject,
    mut v_x_1675_: *mut leanh::LeanObject,
    mut v_00_u03b3_1676_: *mut leanh::LeanObject,
    mut v_f_1677_: *mut leanh::LeanObject,
    mut v_h_1678_: *mut leanh::LeanObject,
    mut v_m_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = leanh::lean_apply_1(v_f_1677_, v_m_1679_);
    return v___x_1680_;
}
pub unsafe fn l_Std_ExtDHashMap_lift___boxed(
    mut v_00_u03b1_1681_: *mut leanh::LeanObject,
    mut v_00_u03b2_1682_: *mut leanh::LeanObject,
    mut v_x_1683_: *mut leanh::LeanObject,
    mut v_x_1684_: *mut leanh::LeanObject,
    mut v_00_u03b3_1685_: *mut leanh::LeanObject,
    mut v_f_1686_: *mut leanh::LeanObject,
    mut v_h_1687_: *mut leanh::LeanObject,
    mut v_m_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_x_1684_);
    leanh::lean_dec_ref(v_x_1683_);
    return v_res_1689_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082___redArg(
    mut v_f_1690_: *mut leanh::LeanObject,
    mut v_m_u2081_1691_: *mut leanh::LeanObject,
    mut v_m_u2082_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1693_ = leanh::lean_apply_2(v_f_1690_, v_m_u2081_1691_, v_m_u2082_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082(
    mut v_00_u03b1_1694_: *mut leanh::LeanObject,
    mut v_00_u03b2_1695_: *mut leanh::LeanObject,
    mut v_x_1696_: *mut leanh::LeanObject,
    mut v_x_1697_: *mut leanh::LeanObject,
    mut v_00_u03b3_1698_: *mut leanh::LeanObject,
    mut v_f_1699_: *mut leanh::LeanObject,
    mut v_h_1700_: *mut leanh::LeanObject,
    mut v_m_u2081_1701_: *mut leanh::LeanObject,
    mut v_m_u2082_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1703_ = leanh::lean_apply_2(v_f_1699_, v_m_u2081_1701_, v_m_u2082_1702_);
    return v___x_1703_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082___boxed(
    mut v_00_u03b1_1704_: *mut leanh::LeanObject,
    mut v_00_u03b2_1705_: *mut leanh::LeanObject,
    mut v_x_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
    mut v_00_u03b3_1708_: *mut leanh::LeanObject,
    mut v_f_1709_: *mut leanh::LeanObject,
    mut v_h_1710_: *mut leanh::LeanObject,
    mut v_m_u2081_1711_: *mut leanh::LeanObject,
    mut v_m_u2082_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_x_1707_);
    leanh::lean_dec_ref(v_x_1706_);
    return v_res_1713_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn___redArg(
    mut v_m_1714_: *mut leanh::LeanObject,
    mut v_f_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = leanh::lean_apply_2(v_f_1715_, v_m_1714_, leanh::lean_box(0));
    return v___x_1716_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn(
    mut v_00_u03b1_1717_: *mut leanh::LeanObject,
    mut v_00_u03b2_1718_: *mut leanh::LeanObject,
    mut v_x_1719_: *mut leanh::LeanObject,
    mut v_x_1720_: *mut leanh::LeanObject,
    mut v_00_u03b3_1721_: *mut leanh::LeanObject,
    mut v_m_1722_: *mut leanh::LeanObject,
    mut v_f_1723_: *mut leanh::LeanObject,
    mut v_h_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = leanh::lean_apply_2(v_f_1723_, v_m_1722_, leanh::lean_box(0));
    return v___x_1725_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn___boxed(
    mut v_00_u03b1_1726_: *mut leanh::LeanObject,
    mut v_00_u03b2_1727_: *mut leanh::LeanObject,
    mut v_x_1728_: *mut leanh::LeanObject,
    mut v_x_1729_: *mut leanh::LeanObject,
    mut v_00_u03b3_1730_: *mut leanh::LeanObject,
    mut v_m_1731_: *mut leanh::LeanObject,
    mut v_f_1732_: *mut leanh::LeanObject,
    mut v_h_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_x_1729_);
    leanh::lean_dec_ref(v_x_1728_);
    return v_res_1734_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___redArg(
    mut v_capacity_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = leanh::lean_unsigned_to_nat(0);
    v___x_1737_ = leanh::lean_unsigned_to_nat(4);
    v___x_1738_ = lean_nat_mul(v_capacity_1735_, v___x_1737_);
    v___x_1739_ = leanh::lean_unsigned_to_nat(3);
    v___x_1740_ = lean_nat_div(v___x_1738_, v___x_1739_);
    leanh::lean_dec(v___x_1738_);
    v___x_1741_ = l_Nat_nextPowerOfTwo(v___x_1740_);
    leanh::lean_dec(v___x_1740_);
    v___x_1742_ = leanh::lean_box(0);
    v___x_1743_ = lean_mk_array(v___x_1741_, v___x_1742_);
    v___x_1744_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1744_, 0, v___x_1736_);
    leanh::lean_ctor_set(v___x_1744_, 1, v___x_1743_);
    return v___x_1744_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___redArg___boxed(
    mut v_capacity_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Std_ExtDHashMap_emptyWithCapacity___redArg(v_capacity_1745_);
    leanh::lean_dec(v_capacity_1745_);
    return v_res_1746_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity(
    mut v_00_u03b1_1747_: *mut leanh::LeanObject,
    mut v_00_u03b2_1748_: *mut leanh::LeanObject,
    mut v_inst_1749_: *mut leanh::LeanObject,
    mut v_inst_1750_: *mut leanh::LeanObject,
    mut v_capacity_1751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1752_ = leanh::lean_unsigned_to_nat(0);
    v___x_1753_ = leanh::lean_unsigned_to_nat(4);
    v___x_1754_ = lean_nat_mul(v_capacity_1751_, v___x_1753_);
    v___x_1755_ = leanh::lean_unsigned_to_nat(3);
    v___x_1756_ = lean_nat_div(v___x_1754_, v___x_1755_);
    leanh::lean_dec(v___x_1754_);
    v___x_1757_ = l_Nat_nextPowerOfTwo(v___x_1756_);
    leanh::lean_dec(v___x_1756_);
    v___x_1758_ = leanh::lean_box(0);
    v___x_1759_ = lean_mk_array(v___x_1757_, v___x_1758_);
    v___x_1760_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1760_, 0, v___x_1752_);
    leanh::lean_ctor_set(v___x_1760_, 1, v___x_1759_);
    return v___x_1760_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___boxed(
    mut v_00_u03b1_1761_: *mut leanh::LeanObject,
    mut v_00_u03b2_1762_: *mut leanh::LeanObject,
    mut v_inst_1763_: *mut leanh::LeanObject,
    mut v_inst_1764_: *mut leanh::LeanObject,
    mut v_capacity_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Std_ExtDHashMap_emptyWithCapacity(
        v_00_u03b1_1761_,
        v_00_u03b2_1762_,
        v_inst_1763_,
        v_inst_1764_,
        v_capacity_1765_,
    );
    leanh::lean_dec(v_capacity_1765_);
    leanh::lean_dec_ref(v_inst_1764_);
    leanh::lean_dec_ref(v_inst_1763_);
    return v_res_1766_;
}
pub unsafe fn _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ = leanh::lean_box(0);
    v___x_1768_ = leanh::lean_unsigned_to_nat(16);
    v___x_1769_ = lean_mk_array(v___x_1768_, v___x_1767_);
    return v___x_1769_;
}
pub unsafe fn _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__0_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0,
    );
    v___x_1771_ = leanh::lean_unsigned_to_nat(0);
    v___x_1772_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    leanh::lean_ctor_set(v___x_1772_, 1, v___x_1770_);
    return v___x_1772_;
}
pub unsafe fn l_Std_ExtDHashMap_instEmptyCollection(
    mut v_00_u03b1_1773_: *mut leanh::LeanObject,
    mut v_00_u03b2_1774_: *mut leanh::LeanObject,
    mut v_inst_1775_: *mut leanh::LeanObject,
    mut v_inst_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    return v___x_1777_;
}
pub unsafe fn l_Std_ExtDHashMap_instEmptyCollection___boxed(
    mut v_00_u03b1_1778_: *mut leanh::LeanObject,
    mut v_00_u03b2_1779_: *mut leanh::LeanObject,
    mut v_inst_1780_: *mut leanh::LeanObject,
    mut v_inst_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Std_ExtDHashMap_instEmptyCollection(
        v_00_u03b1_1778_,
        v_00_u03b2_1779_,
        v_inst_1780_,
        v_inst_1781_,
    );
    leanh::lean_dec_ref(v_inst_1781_);
    leanh::lean_dec_ref(v_inst_1780_);
    return v_res_1782_;
}
pub unsafe fn l_Std_ExtDHashMap_instInhabited(
    mut v_00_u03b1_1783_: *mut leanh::LeanObject,
    mut v_00_u03b2_1784_: *mut leanh::LeanObject,
    mut v_inst_1785_: *mut leanh::LeanObject,
    mut v_inst_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1787_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    return v___x_1787_;
}
pub unsafe fn l_Std_ExtDHashMap_instInhabited___boxed(
    mut v_00_u03b1_1788_: *mut leanh::LeanObject,
    mut v_00_u03b2_1789_: *mut leanh::LeanObject,
    mut v_inst_1790_: *mut leanh::LeanObject,
    mut v_inst_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1792_ = l_Std_ExtDHashMap_instInhabited(
        v_00_u03b1_1788_,
        v_00_u03b2_1789_,
        v_inst_1790_,
        v_inst_1791_,
    );
    leanh::lean_dec_ref(v_inst_1791_);
    leanh::lean_dec_ref(v_inst_1790_);
    return v_res_1792_;
}
pub unsafe fn l_Std_ExtDHashMap_insert___redArg(
    mut v_x_1793_: *mut leanh::LeanObject,
    mut v_x_1794_: *mut leanh::LeanObject,
    mut v_m_1795_: *mut leanh::LeanObject,
    mut v_a_1796_: *mut leanh::LeanObject,
    mut v_b_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1793_, v_x_1794_, v_m_1795_, v_a_1796_, v_b_1797_,
    );
    return v___x_1798_;
}
pub unsafe fn l_Std_ExtDHashMap_insert(
    mut v_00_u03b1_1799_: *mut leanh::LeanObject,
    mut v_00_u03b2_1800_: *mut leanh::LeanObject,
    mut v_x_1801_: *mut leanh::LeanObject,
    mut v_x_1802_: *mut leanh::LeanObject,
    mut v_inst_1803_: *mut leanh::LeanObject,
    mut v_inst_1804_: *mut leanh::LeanObject,
    mut v_m_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
    mut v_b_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1808_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1801_, v_x_1802_, v_m_1805_, v_a_1806_, v_b_1807_,
    );
    return v___x_1808_;
}
pub unsafe fn l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1809_: *mut leanh::LeanObject,
    mut v_x_1810_: *mut leanh::LeanObject,
    mut v_x_1811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1812_ = leanh::lean_ctor_get(v_x_1811_, 0);
    leanh::lean_inc(v_fst_1812_);
    v_snd_1813_ = leanh::lean_ctor_get(v_x_1811_, 1);
    leanh::lean_inc(v_snd_1813_);
    leanh::lean_dec_ref(v_x_1811_);
    v___x_1814_ = leanh::lean_obj_once(
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
    mut v_x_1816_: *mut leanh::LeanObject,
    mut v_x_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1818_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1818_, 0, v_x_1816_);
    leanh::lean_closure_set(v___f_1818_, 1, v_x_1817_);
    return v___f_1818_;
}
pub unsafe fn l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1819_: *mut leanh::LeanObject,
    mut v_00_u03b2_1820_: *mut leanh::LeanObject,
    mut v_x_1821_: *mut leanh::LeanObject,
    mut v_x_1822_: *mut leanh::LeanObject,
    mut v_inst_1823_: *mut leanh::LeanObject,
    mut v_inst_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1825_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1825_, 0, v_x_1821_);
    leanh::lean_closure_set(v___f_1825_, 1, v_x_1822_);
    return v___f_1825_;
}
pub unsafe fn l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1826_: *mut leanh::LeanObject,
    mut v_x_1827_: *mut leanh::LeanObject,
    mut v_x_1828_: *mut leanh::LeanObject,
    mut v_x_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1830_ = leanh::lean_ctor_get(v_x_1828_, 0);
    leanh::lean_inc(v_fst_1830_);
    v_snd_1831_ = leanh::lean_ctor_get(v_x_1828_, 1);
    leanh::lean_inc(v_snd_1831_);
    leanh::lean_dec_ref(v_x_1828_);
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
    mut v_x_1833_: *mut leanh::LeanObject,
    mut v_x_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1835_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1835_, 0, v_x_1833_);
    leanh::lean_closure_set(v___f_1835_, 1, v_x_1834_);
    return v___f_1835_;
}
pub unsafe fn l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1836_: *mut leanh::LeanObject,
    mut v_00_u03b2_1837_: *mut leanh::LeanObject,
    mut v_x_1838_: *mut leanh::LeanObject,
    mut v_x_1839_: *mut leanh::LeanObject,
    mut v_inst_1840_: *mut leanh::LeanObject,
    mut v_inst_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1842_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1842_, 0, v_x_1838_);
    leanh::lean_closure_set(v___f_1842_, 1, v_x_1839_);
    return v___f_1842_;
}
pub unsafe fn l_Std_ExtDHashMap_insertIfNew___redArg(
    mut v_x_1843_: *mut leanh::LeanObject,
    mut v_x_1844_: *mut leanh::LeanObject,
    mut v_m_1845_: *mut leanh::LeanObject,
    mut v_a_1846_: *mut leanh::LeanObject,
    mut v_b_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1843_, v_x_1844_, v_m_1845_, v_a_1846_, v_b_1847_,
    );
    return v___x_1848_;
}
pub unsafe fn l_Std_ExtDHashMap_insertIfNew(
    mut v_00_u03b1_1849_: *mut leanh::LeanObject,
    mut v_00_u03b2_1850_: *mut leanh::LeanObject,
    mut v_x_1851_: *mut leanh::LeanObject,
    mut v_x_1852_: *mut leanh::LeanObject,
    mut v_inst_1853_: *mut leanh::LeanObject,
    mut v_inst_1854_: *mut leanh::LeanObject,
    mut v_m_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
    mut v_b_1857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1851_, v_x_1852_, v_m_1855_, v_a_1856_, v_b_1857_,
    );
    return v___x_1858_;
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsert___redArg(
    mut v_x_1859_: *mut leanh::LeanObject,
    mut v_x_1860_: *mut leanh::LeanObject,
    mut v_m_1861_: *mut leanh::LeanObject,
    mut v_a_1862_: *mut leanh::LeanObject,
    mut v_b_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1868_: u8 = 0;
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v_val_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1864_ = leanh::lean_ctor_get(v_m_1861_, 0);
                v_buckets_1865_ = leanh::lean_ctor_get(v_m_1861_, 1);
                v_isSharedCheck_1916_ = (!leanh::lean_is_exclusive(v_m_1861_)) as u8;
                if v_isSharedCheck_1916_ == 0 {
                    v___x_1867_ = v_m_1861_;
                    v_isShared_1868_ = v_isSharedCheck_1916_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1865_);
                    leanh::lean_inc(v_size_1864_);
                    leanh::lean_dec(v_m_1861_);
                    v___x_1867_ = leanh::lean_box(0);
                    v_isShared_1868_ = v_isSharedCheck_1916_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1869_ = lean_array_get_size(v_buckets_1865_);
                leanh::lean_inc_ref(v_x_1860_);
                leanh::lean_inc_n(v_a_1862_, 2);
                v___x_1870_ = leanh::lean_apply_1(v_x_1860_, v_a_1862_);
                v___x_1871_ = 32u64;
                v___x_1872_ = leanh::lean_unbox_uint64(v___x_1870_);
                v___x_1873_ = lean_uint64_shift_right(v___x_1872_, v___x_1871_);
                v___x_1874_ = leanh::lean_unbox_uint64(v___x_1870_);
                leanh::lean_dec_ref(v___x_1870_);
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
                leanh::lean_inc(v_bkt_1884_);
                leanh::lean_inc_ref(v_x_1859_);
                v___x_1885_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1859_,
                    v_a_1862_,
                    v_bkt_1884_,
                );
                if v___x_1885_ == 0 {
                    leanh::lean_dec_ref(v_x_1859_);
                    v___x_1886_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1887_ = lean_nat_add(v_size_1864_, v___x_1886_);
                    leanh::lean_dec(v_size_1864_);
                    leanh::lean_inc(v_bkt_1884_);
                    v___x_1888_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1888_, 0, v_a_1862_);
                    leanh::lean_ctor_set(v___x_1888_, 1, v_b_1863_);
                    leanh::lean_ctor_set(v___x_1888_, 2, v_bkt_1884_);
                    v_buckets_x27_1889_ =
                        lean_array_uset(v_buckets_1865_, v___x_1883_, v___x_1888_);
                    v___x_1890_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1891_ = lean_nat_mul(v_size_x27_1887_, v___x_1890_);
                    v___x_1892_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1893_ = lean_nat_div(v___x_1891_, v___x_1892_);
                    leanh::lean_dec(v___x_1891_);
                    v___x_1894_ = lean_array_get_size(v_buckets_x27_1889_);
                    v___x_1895_ = lean_nat_dec_le(v___x_1893_, v___x_1894_);
                    leanh::lean_dec(v___x_1893_);
                    if v___x_1895_ == 0 {
                        v_val_1896_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_1860_,
                            v_buckets_x27_1889_,
                        );
                        if v_isShared_1868_ == 0 {
                            leanh::lean_ctor_set(v___x_1867_, 1, v_val_1896_);
                            leanh::lean_ctor_set(v___x_1867_, 0, v_size_x27_1887_);
                            v___x_1898_ = v___x_1867_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1901_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1901_,
                                0,
                                v_size_x27_1887_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_val_1896_);
                            v___x_1898_ = v_reuseFailAlloc_1901_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_1860_);
                        if v_isShared_1868_ == 0 {
                            leanh::lean_ctor_set(v___x_1867_, 1, v_buckets_x27_1889_);
                            leanh::lean_ctor_set(v___x_1867_, 0, v_size_x27_1887_);
                            v___x_1903_ = v___x_1867_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1906_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1906_,
                                0,
                                v_size_x27_1887_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_1884_);
                    leanh::lean_dec_ref(v_x_1860_);
                    v___x_1907_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_1867_, 1, v___x_1910_);
                        v___x_1912_ = v___x_1867_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1915_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_size_1864_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1910_);
                        v___x_1912_ = v_reuseFailAlloc_1915_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1899_ = leanh::lean_box((v___x_1885_) as usize);
                v___x_1900_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1900_, 0, v___x_1899_);
                leanh::lean_ctor_set(v___x_1900_, 1, v___x_1898_);
                return v___x_1900_;
            }
            3 => {
                v___x_1904_ = leanh::lean_box((v___x_1885_) as usize);
                v___x_1905_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                leanh::lean_ctor_set(v___x_1905_, 1, v___x_1903_);
                return v___x_1905_;
            }
            4 => {
                v___x_1913_ = leanh::lean_box((v___x_1885_) as usize);
                v___x_1914_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1914_, 0, v___x_1913_);
                leanh::lean_ctor_set(v___x_1914_, 1, v___x_1912_);
                return v___x_1914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsert(
    mut v_00_u03b1_1917_: *mut leanh::LeanObject,
    mut v_00_u03b2_1918_: *mut leanh::LeanObject,
    mut v_x_1919_: *mut leanh::LeanObject,
    mut v_x_1920_: *mut leanh::LeanObject,
    mut v_inst_1921_: *mut leanh::LeanObject,
    mut v_inst_1922_: *mut leanh::LeanObject,
    mut v_m_1923_: *mut leanh::LeanObject,
    mut v_a_1924_: *mut leanh::LeanObject,
    mut v_b_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: u8 = 0;
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v_val_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1926_ = leanh::lean_ctor_get(v_m_1923_, 0);
                v_buckets_1927_ = leanh::lean_ctor_get(v_m_1923_, 1);
                v_isSharedCheck_1978_ = (!leanh::lean_is_exclusive(v_m_1923_)) as u8;
                if v_isSharedCheck_1978_ == 0 {
                    v___x_1929_ = v_m_1923_;
                    v_isShared_1930_ = v_isSharedCheck_1978_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1927_);
                    leanh::lean_inc(v_size_1926_);
                    leanh::lean_dec(v_m_1923_);
                    v___x_1929_ = leanh::lean_box(0);
                    v_isShared_1930_ = v_isSharedCheck_1978_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1931_ = lean_array_get_size(v_buckets_1927_);
                leanh::lean_inc_ref(v_x_1920_);
                leanh::lean_inc_n(v_a_1924_, 2);
                v___x_1932_ = leanh::lean_apply_1(v_x_1920_, v_a_1924_);
                v___x_1933_ = 32u64;
                v___x_1934_ = leanh::lean_unbox_uint64(v___x_1932_);
                v___x_1935_ = lean_uint64_shift_right(v___x_1934_, v___x_1933_);
                v___x_1936_ = leanh::lean_unbox_uint64(v___x_1932_);
                leanh::lean_dec_ref(v___x_1932_);
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
                leanh::lean_inc(v_bkt_1946_);
                leanh::lean_inc_ref(v_x_1919_);
                v___x_1947_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1919_,
                    v_a_1924_,
                    v_bkt_1946_,
                );
                if v___x_1947_ == 0 {
                    leanh::lean_dec_ref(v_x_1919_);
                    v___x_1948_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1949_ = lean_nat_add(v_size_1926_, v___x_1948_);
                    leanh::lean_dec(v_size_1926_);
                    leanh::lean_inc(v_bkt_1946_);
                    v___x_1950_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1950_, 0, v_a_1924_);
                    leanh::lean_ctor_set(v___x_1950_, 1, v_b_1925_);
                    leanh::lean_ctor_set(v___x_1950_, 2, v_bkt_1946_);
                    v_buckets_x27_1951_ =
                        lean_array_uset(v_buckets_1927_, v___x_1945_, v___x_1950_);
                    v___x_1952_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1953_ = lean_nat_mul(v_size_x27_1949_, v___x_1952_);
                    v___x_1954_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1955_ = lean_nat_div(v___x_1953_, v___x_1954_);
                    leanh::lean_dec(v___x_1953_);
                    v___x_1956_ = lean_array_get_size(v_buckets_x27_1951_);
                    v___x_1957_ = lean_nat_dec_le(v___x_1955_, v___x_1956_);
                    leanh::lean_dec(v___x_1955_);
                    if v___x_1957_ == 0 {
                        v_val_1958_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_1920_,
                            v_buckets_x27_1951_,
                        );
                        if v_isShared_1930_ == 0 {
                            leanh::lean_ctor_set(v___x_1929_, 1, v_val_1958_);
                            leanh::lean_ctor_set(v___x_1929_, 0, v_size_x27_1949_);
                            v___x_1960_ = v___x_1929_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1963_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1963_,
                                0,
                                v_size_x27_1949_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_val_1958_);
                            v___x_1960_ = v_reuseFailAlloc_1963_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_1920_);
                        if v_isShared_1930_ == 0 {
                            leanh::lean_ctor_set(v___x_1929_, 1, v_buckets_x27_1951_);
                            leanh::lean_ctor_set(v___x_1929_, 0, v_size_x27_1949_);
                            v___x_1965_ = v___x_1929_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1968_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1968_,
                                0,
                                v_size_x27_1949_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_1946_);
                    leanh::lean_dec_ref(v_x_1920_);
                    v___x_1969_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_1929_, 1, v___x_1972_);
                        v___x_1974_ = v___x_1929_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1977_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_size_1926_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1972_);
                        v___x_1974_ = v_reuseFailAlloc_1977_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1961_ = leanh::lean_box((v___x_1947_) as usize);
                v___x_1962_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1962_, 0, v___x_1961_);
                leanh::lean_ctor_set(v___x_1962_, 1, v___x_1960_);
                return v___x_1962_;
            }
            3 => {
                v___x_1966_ = leanh::lean_box((v___x_1947_) as usize);
                v___x_1967_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1967_, 0, v___x_1966_);
                leanh::lean_ctor_set(v___x_1967_, 1, v___x_1965_);
                return v___x_1967_;
            }
            4 => {
                v___x_1975_ = leanh::lean_box((v___x_1947_) as usize);
                v___x_1976_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1976_, 0, v___x_1975_);
                leanh::lean_ctor_set(v___x_1976_, 1, v___x_1974_);
                return v___x_1976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsertIfNew___redArg(
    mut v_x_1979_: *mut leanh::LeanObject,
    mut v_x_1980_: *mut leanh::LeanObject,
    mut v_m_1981_: *mut leanh::LeanObject,
    mut v_a_1982_: *mut leanh::LeanObject,
    mut v_b_1983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: u8 = 0;
    let mut v_val_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2027_: u8 = 0;
    let mut v_unused_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1984_ = leanh::lean_ctor_get(v_m_1981_, 0);
                v_buckets_1985_ = leanh::lean_ctor_get(v_m_1981_, 1);
                v___x_1986_ = lean_array_get_size(v_buckets_1985_);
                leanh::lean_inc_ref(v_x_1980_);
                leanh::lean_inc_n(v_a_1982_, 2);
                v___x_1987_ = leanh::lean_apply_1(v_x_1980_, v_a_1982_);
                v___x_1988_ = 32u64;
                v___x_1989_ = leanh::lean_unbox_uint64(v___x_1987_);
                v___x_1990_ = lean_uint64_shift_right(v___x_1989_, v___x_1988_);
                v___x_1991_ = leanh::lean_unbox_uint64(v___x_1987_);
                leanh::lean_dec_ref(v___x_1987_);
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
                leanh::lean_inc(v_bkt_2001_);
                v___x_2002_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1979_,
                    v_a_1982_,
                    v_bkt_2001_,
                );
                if v___x_2002_ == 0 {
                    leanh::lean_inc_ref(v_buckets_1985_);
                    leanh::lean_inc(v_size_1984_);
                    v_isSharedCheck_2027_ = (!leanh::lean_is_exclusive(v_m_1981_)) as u8;
                    if v_isSharedCheck_2027_ == 0 {
                        v_unused_2028_ = leanh::lean_ctor_get(v_m_1981_, 1);
                        leanh::lean_dec(v_unused_2028_);
                        v_unused_2029_ = leanh::lean_ctor_get(v_m_1981_, 0);
                        leanh::lean_dec(v_unused_2029_);
                        v___x_2004_ = v_m_1981_;
                        v_isShared_2005_ = v_isSharedCheck_2027_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_1981_);
                        v___x_2004_ = leanh::lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2027_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_1983_);
                    leanh::lean_dec(v_a_1982_);
                    leanh::lean_dec_ref(v_x_1980_);
                    v___x_2030_ = leanh::lean_box((v___x_2002_) as usize);
                    v___x_2031_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2031_, 0, v___x_2030_);
                    leanh::lean_ctor_set(v___x_2031_, 1, v_m_1981_);
                    return v___x_2031_;
                }
            }
            1 => {
                v___x_2006_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2007_ = lean_nat_add(v_size_1984_, v___x_2006_);
                leanh::lean_dec(v_size_1984_);
                leanh::lean_inc(v_bkt_2001_);
                v___x_2008_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2008_, 0, v_a_1982_);
                leanh::lean_ctor_set(v___x_2008_, 1, v_b_1983_);
                leanh::lean_ctor_set(v___x_2008_, 2, v_bkt_2001_);
                v_buckets_x27_2009_ = lean_array_uset(v_buckets_1985_, v___x_2000_, v___x_2008_);
                v___x_2010_ = leanh::lean_unsigned_to_nat(4);
                v___x_2011_ = lean_nat_mul(v_size_x27_2007_, v___x_2010_);
                v___x_2012_ = leanh::lean_unsigned_to_nat(3);
                v___x_2013_ = lean_nat_div(v___x_2011_, v___x_2012_);
                leanh::lean_dec(v___x_2011_);
                v___x_2014_ = lean_array_get_size(v_buckets_x27_2009_);
                v___x_2015_ = lean_nat_dec_le(v___x_2013_, v___x_2014_);
                leanh::lean_dec(v___x_2013_);
                if v___x_2015_ == 0 {
                    v_val_2016_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1980_,
                        v_buckets_x27_2009_,
                    );
                    if v_isShared_2005_ == 0 {
                        leanh::lean_ctor_set(v___x_2004_, 1, v_val_2016_);
                        leanh::lean_ctor_set(v___x_2004_, 0, v_size_x27_2007_);
                        v___x_2018_ = v___x_2004_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_size_x27_2007_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_val_2016_);
                        v___x_2018_ = v_reuseFailAlloc_2021_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1980_);
                    if v_isShared_2005_ == 0 {
                        leanh::lean_ctor_set(v___x_2004_, 1, v_buckets_x27_2009_);
                        leanh::lean_ctor_set(v___x_2004_, 0, v_size_x27_2007_);
                        v___x_2023_ = v___x_2004_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2026_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_size_x27_2007_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_buckets_x27_2009_);
                        v___x_2023_ = v_reuseFailAlloc_2026_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2019_ = leanh::lean_box((v___x_2002_) as usize);
                v___x_2020_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2020_, 0, v___x_2019_);
                leanh::lean_ctor_set(v___x_2020_, 1, v___x_2018_);
                return v___x_2020_;
            }
            3 => {
                v___x_2024_ = leanh::lean_box((v___x_2002_) as usize);
                v___x_2025_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2025_, 0, v___x_2024_);
                leanh::lean_ctor_set(v___x_2025_, 1, v___x_2023_);
                return v___x_2025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsertIfNew(
    mut v_00_u03b1_2032_: *mut leanh::LeanObject,
    mut v_00_u03b2_2033_: *mut leanh::LeanObject,
    mut v_x_2034_: *mut leanh::LeanObject,
    mut v_x_2035_: *mut leanh::LeanObject,
    mut v_inst_2036_: *mut leanh::LeanObject,
    mut v_inst_2037_: *mut leanh::LeanObject,
    mut v_m_2038_: *mut leanh::LeanObject,
    mut v_a_2039_: *mut leanh::LeanObject,
    mut v_b_2040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v_val_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_unused_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2041_ = leanh::lean_ctor_get(v_m_2038_, 0);
                v_buckets_2042_ = leanh::lean_ctor_get(v_m_2038_, 1);
                v___x_2043_ = lean_array_get_size(v_buckets_2042_);
                leanh::lean_inc_ref(v_x_2035_);
                leanh::lean_inc_n(v_a_2039_, 2);
                v___x_2044_ = leanh::lean_apply_1(v_x_2035_, v_a_2039_);
                v___x_2045_ = 32u64;
                v___x_2046_ = leanh::lean_unbox_uint64(v___x_2044_);
                v___x_2047_ = lean_uint64_shift_right(v___x_2046_, v___x_2045_);
                v___x_2048_ = leanh::lean_unbox_uint64(v___x_2044_);
                leanh::lean_dec_ref(v___x_2044_);
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
                leanh::lean_inc(v_bkt_2058_);
                v___x_2059_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_2034_,
                    v_a_2039_,
                    v_bkt_2058_,
                );
                if v___x_2059_ == 0 {
                    leanh::lean_inc_ref(v_buckets_2042_);
                    leanh::lean_inc(v_size_2041_);
                    v_isSharedCheck_2084_ = (!leanh::lean_is_exclusive(v_m_2038_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v_unused_2085_ = leanh::lean_ctor_get(v_m_2038_, 1);
                        leanh::lean_dec(v_unused_2085_);
                        v_unused_2086_ = leanh::lean_ctor_get(v_m_2038_, 0);
                        leanh::lean_dec(v_unused_2086_);
                        v___x_2061_ = v_m_2038_;
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2038_);
                        v___x_2061_ = leanh::lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2040_);
                    leanh::lean_dec(v_a_2039_);
                    leanh::lean_dec_ref(v_x_2035_);
                    v___x_2087_ = leanh::lean_box((v___x_2059_) as usize);
                    v___x_2088_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                    leanh::lean_ctor_set(v___x_2088_, 1, v_m_2038_);
                    return v___x_2088_;
                }
            }
            1 => {
                v___x_2063_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2064_ = lean_nat_add(v_size_2041_, v___x_2063_);
                leanh::lean_dec(v_size_2041_);
                leanh::lean_inc(v_bkt_2058_);
                v___x_2065_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2065_, 0, v_a_2039_);
                leanh::lean_ctor_set(v___x_2065_, 1, v_b_2040_);
                leanh::lean_ctor_set(v___x_2065_, 2, v_bkt_2058_);
                v_buckets_x27_2066_ = lean_array_uset(v_buckets_2042_, v___x_2057_, v___x_2065_);
                v___x_2067_ = leanh::lean_unsigned_to_nat(4);
                v___x_2068_ = lean_nat_mul(v_size_x27_2064_, v___x_2067_);
                v___x_2069_ = leanh::lean_unsigned_to_nat(3);
                v___x_2070_ = lean_nat_div(v___x_2068_, v___x_2069_);
                leanh::lean_dec(v___x_2068_);
                v___x_2071_ = lean_array_get_size(v_buckets_x27_2066_);
                v___x_2072_ = lean_nat_dec_le(v___x_2070_, v___x_2071_);
                leanh::lean_dec(v___x_2070_);
                if v___x_2072_ == 0 {
                    v_val_2073_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2035_,
                        v_buckets_x27_2066_,
                    );
                    if v_isShared_2062_ == 0 {
                        leanh::lean_ctor_set(v___x_2061_, 1, v_val_2073_);
                        leanh::lean_ctor_set(v___x_2061_, 0, v_size_x27_2064_);
                        v___x_2075_ = v___x_2061_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2078_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_size_x27_2064_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_val_2073_);
                        v___x_2075_ = v_reuseFailAlloc_2078_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2035_);
                    if v_isShared_2062_ == 0 {
                        leanh::lean_ctor_set(v___x_2061_, 1, v_buckets_x27_2066_);
                        leanh::lean_ctor_set(v___x_2061_, 0, v_size_x27_2064_);
                        v___x_2080_ = v___x_2061_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2083_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_size_x27_2064_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_buckets_x27_2066_);
                        v___x_2080_ = v_reuseFailAlloc_2083_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2076_ = leanh::lean_box((v___x_2059_) as usize);
                v___x_2077_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2077_, 0, v___x_2076_);
                leanh::lean_ctor_set(v___x_2077_, 1, v___x_2075_);
                return v___x_2077_;
            }
            3 => {
                v___x_2081_ = leanh::lean_box((v___x_2059_) as usize);
                v___x_2082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2082_, 0, v___x_2081_);
                leanh::lean_ctor_set(v___x_2082_, 1, v___x_2080_);
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getThenInsertIfNew_x3f___redArg(
    mut v_x_2089_: *mut leanh::LeanObject,
    mut v_x_2090_: *mut leanh::LeanObject,
    mut v_m_2091_: *mut leanh::LeanObject,
    mut v_a_2092_: *mut leanh::LeanObject,
    mut v_b_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: u8 = 0;
    let mut v_val_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2094_ = leanh::lean_ctor_get(v_m_2091_, 0);
                v_buckets_2095_ = leanh::lean_ctor_get(v_m_2091_, 1);
                v___x_2096_ = lean_array_get_size(v_buckets_2095_);
                leanh::lean_inc_ref(v_x_2090_);
                leanh::lean_inc_n(v_a_2092_, 2);
                v___x_2097_ = leanh::lean_apply_1(v_x_2090_, v_a_2092_);
                v___x_2098_ = 32u64;
                v___x_2099_ = leanh::lean_unbox_uint64(v___x_2097_);
                v___x_2100_ = lean_uint64_shift_right(v___x_2099_, v___x_2098_);
                v___x_2101_ = leanh::lean_unbox_uint64(v___x_2097_);
                leanh::lean_dec_ref(v___x_2097_);
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
                leanh::lean_inc(v_bkt_2111_);
                v___x_2112_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_x_2089_,
                    v_a_2092_,
                    v_bkt_2111_,
                );
                if leanh::lean_obj_tag(v___x_2112_) == 0 {
                    leanh::lean_inc_ref(v_buckets_2095_);
                    leanh::lean_inc(v_size_2094_);
                    v_isSharedCheck_2135_ = (!leanh::lean_is_exclusive(v_m_2091_)) as u8;
                    if v_isSharedCheck_2135_ == 0 {
                        v_unused_2136_ = leanh::lean_ctor_get(v_m_2091_, 1);
                        leanh::lean_dec(v_unused_2136_);
                        v_unused_2137_ = leanh::lean_ctor_get(v_m_2091_, 0);
                        leanh::lean_dec(v_unused_2137_);
                        v___x_2114_ = v_m_2091_;
                        v_isShared_2115_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2091_);
                        v___x_2114_ = leanh::lean_box(0);
                        v_isShared_2115_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2093_);
                    leanh::lean_dec(v_a_2092_);
                    leanh::lean_dec_ref(v_x_2090_);
                    v___x_2138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2138_, 0, v___x_2112_);
                    leanh::lean_ctor_set(v___x_2138_, 1, v_m_2091_);
                    return v___x_2138_;
                }
            }
            1 => {
                v___x_2116_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2117_ = lean_nat_add(v_size_2094_, v___x_2116_);
                leanh::lean_dec(v_size_2094_);
                leanh::lean_inc(v_bkt_2111_);
                v___x_2118_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2118_, 0, v_a_2092_);
                leanh::lean_ctor_set(v___x_2118_, 1, v_b_2093_);
                leanh::lean_ctor_set(v___x_2118_, 2, v_bkt_2111_);
                v_buckets_x27_2119_ = lean_array_uset(v_buckets_2095_, v___x_2110_, v___x_2118_);
                v___x_2120_ = leanh::lean_unsigned_to_nat(4);
                v___x_2121_ = lean_nat_mul(v_size_x27_2117_, v___x_2120_);
                v___x_2122_ = leanh::lean_unsigned_to_nat(3);
                v___x_2123_ = lean_nat_div(v___x_2121_, v___x_2122_);
                leanh::lean_dec(v___x_2121_);
                v___x_2124_ = lean_array_get_size(v_buckets_x27_2119_);
                v___x_2125_ = lean_nat_dec_le(v___x_2123_, v___x_2124_);
                leanh::lean_dec(v___x_2123_);
                if v___x_2125_ == 0 {
                    v_val_2126_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2090_,
                        v_buckets_x27_2119_,
                    );
                    if v_isShared_2115_ == 0 {
                        leanh::lean_ctor_set(v___x_2114_, 1, v_val_2126_);
                        leanh::lean_ctor_set(v___x_2114_, 0, v_size_x27_2117_);
                        v___x_2128_ = v___x_2114_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2130_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_size_x27_2117_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_val_2126_);
                        v___x_2128_ = v_reuseFailAlloc_2130_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2090_);
                    if v_isShared_2115_ == 0 {
                        leanh::lean_ctor_set(v___x_2114_, 1, v_buckets_x27_2119_);
                        leanh::lean_ctor_set(v___x_2114_, 0, v_size_x27_2117_);
                        v___x_2132_ = v___x_2114_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2134_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_size_x27_2117_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_buckets_x27_2119_);
                        v___x_2132_ = v_reuseFailAlloc_2134_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2129_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2129_, 0, v___x_2112_);
                leanh::lean_ctor_set(v___x_2129_, 1, v___x_2128_);
                return v___x_2129_;
            }
            3 => {
                v___x_2133_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2133_, 0, v___x_2112_);
                leanh::lean_ctor_set(v___x_2133_, 1, v___x_2132_);
                return v___x_2133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2139_: *mut leanh::LeanObject,
    mut v_00_u03b2_2140_: *mut leanh::LeanObject,
    mut v_x_2141_: *mut leanh::LeanObject,
    mut v_x_2142_: *mut leanh::LeanObject,
    mut v_inst_2143_: *mut leanh::LeanObject,
    mut v_m_2144_: *mut leanh::LeanObject,
    mut v_a_2145_: *mut leanh::LeanObject,
    mut v_b_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    let mut v_val_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_unused_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2147_ = leanh::lean_ctor_get(v_m_2144_, 0);
                v_buckets_2148_ = leanh::lean_ctor_get(v_m_2144_, 1);
                v___x_2149_ = lean_array_get_size(v_buckets_2148_);
                leanh::lean_inc_ref(v_x_2142_);
                leanh::lean_inc_n(v_a_2145_, 2);
                v___x_2150_ = leanh::lean_apply_1(v_x_2142_, v_a_2145_);
                v___x_2151_ = 32u64;
                v___x_2152_ = leanh::lean_unbox_uint64(v___x_2150_);
                v___x_2153_ = lean_uint64_shift_right(v___x_2152_, v___x_2151_);
                v___x_2154_ = leanh::lean_unbox_uint64(v___x_2150_);
                leanh::lean_dec_ref(v___x_2150_);
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
                leanh::lean_inc(v_bkt_2164_);
                v___x_2165_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_x_2141_,
                    v_a_2145_,
                    v_bkt_2164_,
                );
                if leanh::lean_obj_tag(v___x_2165_) == 0 {
                    leanh::lean_inc_ref(v_buckets_2148_);
                    leanh::lean_inc(v_size_2147_);
                    v_isSharedCheck_2188_ = (!leanh::lean_is_exclusive(v_m_2144_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v_unused_2189_ = leanh::lean_ctor_get(v_m_2144_, 1);
                        leanh::lean_dec(v_unused_2189_);
                        v_unused_2190_ = leanh::lean_ctor_get(v_m_2144_, 0);
                        leanh::lean_dec(v_unused_2190_);
                        v___x_2167_ = v_m_2144_;
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2144_);
                        v___x_2167_ = leanh::lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2146_);
                    leanh::lean_dec(v_a_2145_);
                    leanh::lean_dec_ref(v_x_2142_);
                    v___x_2191_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2191_, 0, v___x_2165_);
                    leanh::lean_ctor_set(v___x_2191_, 1, v_m_2144_);
                    return v___x_2191_;
                }
            }
            1 => {
                v___x_2169_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2170_ = lean_nat_add(v_size_2147_, v___x_2169_);
                leanh::lean_dec(v_size_2147_);
                leanh::lean_inc(v_bkt_2164_);
                v___x_2171_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2171_, 0, v_a_2145_);
                leanh::lean_ctor_set(v___x_2171_, 1, v_b_2146_);
                leanh::lean_ctor_set(v___x_2171_, 2, v_bkt_2164_);
                v_buckets_x27_2172_ = lean_array_uset(v_buckets_2148_, v___x_2163_, v___x_2171_);
                v___x_2173_ = leanh::lean_unsigned_to_nat(4);
                v___x_2174_ = lean_nat_mul(v_size_x27_2170_, v___x_2173_);
                v___x_2175_ = leanh::lean_unsigned_to_nat(3);
                v___x_2176_ = lean_nat_div(v___x_2174_, v___x_2175_);
                leanh::lean_dec(v___x_2174_);
                v___x_2177_ = lean_array_get_size(v_buckets_x27_2172_);
                v___x_2178_ = lean_nat_dec_le(v___x_2176_, v___x_2177_);
                leanh::lean_dec(v___x_2176_);
                if v___x_2178_ == 0 {
                    v_val_2179_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2142_,
                        v_buckets_x27_2172_,
                    );
                    if v_isShared_2168_ == 0 {
                        leanh::lean_ctor_set(v___x_2167_, 1, v_val_2179_);
                        leanh::lean_ctor_set(v___x_2167_, 0, v_size_x27_2170_);
                        v___x_2181_ = v___x_2167_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2183_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_size_x27_2170_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_val_2179_);
                        v___x_2181_ = v_reuseFailAlloc_2183_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2142_);
                    if v_isShared_2168_ == 0 {
                        leanh::lean_ctor_set(v___x_2167_, 1, v_buckets_x27_2172_);
                        leanh::lean_ctor_set(v___x_2167_, 0, v_size_x27_2170_);
                        v___x_2185_ = v___x_2167_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2187_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_size_x27_2170_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_buckets_x27_2172_);
                        v___x_2185_ = v_reuseFailAlloc_2187_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2182_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2182_, 0, v___x_2165_);
                leanh::lean_ctor_set(v___x_2182_, 1, v___x_2181_);
                return v___x_2182_;
            }
            3 => {
                v___x_2186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2186_, 0, v___x_2165_);
                leanh::lean_ctor_set(v___x_2186_, 1, v___x_2185_);
                return v___x_2186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___redArg(
    mut v_x_2192_: *mut leanh::LeanObject,
    mut v_x_2193_: *mut leanh::LeanObject,
    mut v_m_2194_: *mut leanh::LeanObject,
    mut v_a_2195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_x_2192_, v_x_2193_, v_m_2194_, v_a_2195_,
    );
    return v___x_2196_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___redArg___boxed(
    mut v_x_2197_: *mut leanh::LeanObject,
    mut v_x_2198_: *mut leanh::LeanObject,
    mut v_m_2199_: *mut leanh::LeanObject,
    mut v_a_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Std_ExtDHashMap_get_x3f___redArg(v_x_2197_, v_x_2198_, v_m_2199_, v_a_2200_);
    leanh::lean_dec(v_m_2199_);
    return v_res_2201_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f(
    mut v_00_u03b1_2202_: *mut leanh::LeanObject,
    mut v_00_u03b2_2203_: *mut leanh::LeanObject,
    mut v_x_2204_: *mut leanh::LeanObject,
    mut v_x_2205_: *mut leanh::LeanObject,
    mut v_inst_2206_: *mut leanh::LeanObject,
    mut v_m_2207_: *mut leanh::LeanObject,
    mut v_a_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2209_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_x_2204_, v_x_2205_, v_m_2207_, v_a_2208_,
    );
    return v___x_2209_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___boxed(
    mut v_00_u03b1_2210_: *mut leanh::LeanObject,
    mut v_00_u03b2_2211_: *mut leanh::LeanObject,
    mut v_x_2212_: *mut leanh::LeanObject,
    mut v_x_2213_: *mut leanh::LeanObject,
    mut v_inst_2214_: *mut leanh::LeanObject,
    mut v_m_2215_: *mut leanh::LeanObject,
    mut v_a_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2217_ = l_Std_ExtDHashMap_get_x3f(
        v_00_u03b1_2210_,
        v_00_u03b2_2211_,
        v_x_2212_,
        v_x_2213_,
        v_inst_2214_,
        v_m_2215_,
        v_a_2216_,
    );
    leanh::lean_dec(v_m_2215_);
    return v_res_2217_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___redArg(
    mut v_x_2218_: *mut leanh::LeanObject,
    mut v_x_2219_: *mut leanh::LeanObject,
    mut v_m_2220_: *mut leanh::LeanObject,
    mut v_a_2221_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2222_: u8 = 0;
    v___x_2222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2218_, v_x_2219_, v_m_2220_, v_a_2221_,
    );
    return v___x_2222_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___redArg___boxed(
    mut v_x_2223_: *mut leanh::LeanObject,
    mut v_x_2224_: *mut leanh::LeanObject,
    mut v_m_2225_: *mut leanh::LeanObject,
    mut v_a_2226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2227_: u8 = 0;
    let mut v_r_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2227_ = l_Std_ExtDHashMap_contains___redArg(v_x_2223_, v_x_2224_, v_m_2225_, v_a_2226_);
    leanh::lean_dec(v_m_2225_);
    v_r_2228_ = leanh::lean_box((v_res_2227_) as usize);
    return v_r_2228_;
}
pub unsafe fn l_Std_ExtDHashMap_contains(
    mut v_00_u03b1_2229_: *mut leanh::LeanObject,
    mut v_00_u03b2_2230_: *mut leanh::LeanObject,
    mut v_x_2231_: *mut leanh::LeanObject,
    mut v_x_2232_: *mut leanh::LeanObject,
    mut v_inst_2233_: *mut leanh::LeanObject,
    mut v_inst_2234_: *mut leanh::LeanObject,
    mut v_m_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2237_: u8 = 0;
    v___x_2237_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2231_, v_x_2232_, v_m_2235_, v_a_2236_,
    );
    return v___x_2237_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___boxed(
    mut v_00_u03b1_2238_: *mut leanh::LeanObject,
    mut v_00_u03b2_2239_: *mut leanh::LeanObject,
    mut v_x_2240_: *mut leanh::LeanObject,
    mut v_x_2241_: *mut leanh::LeanObject,
    mut v_inst_2242_: *mut leanh::LeanObject,
    mut v_inst_2243_: *mut leanh::LeanObject,
    mut v_m_2244_: *mut leanh::LeanObject,
    mut v_a_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2246_: u8 = 0;
    let mut v_r_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2244_);
    v_r_2247_ = leanh::lean_box((v_res_2246_) as usize);
    return v_r_2247_;
}
pub unsafe fn l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2248_: *mut leanh::LeanObject,
    mut v_00_u03b2_2249_: *mut leanh::LeanObject,
    mut v_x_2250_: *mut leanh::LeanObject,
    mut v_x_2251_: *mut leanh::LeanObject,
    mut v_inst_2252_: *mut leanh::LeanObject,
    mut v_inst_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = leanh::lean_box(0);
    return v___x_2254_;
}
pub unsafe fn l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(
    mut v_00_u03b1_2255_: *mut leanh::LeanObject,
    mut v_00_u03b2_2256_: *mut leanh::LeanObject,
    mut v_x_2257_: *mut leanh::LeanObject,
    mut v_x_2258_: *mut leanh::LeanObject,
    mut v_inst_2259_: *mut leanh::LeanObject,
    mut v_inst_2260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(
        v_00_u03b1_2255_,
        v_00_u03b2_2256_,
        v_x_2257_,
        v_x_2258_,
        v_inst_2259_,
        v_inst_2260_,
    );
    leanh::lean_dec_ref(v_x_2258_);
    leanh::lean_dec_ref(v_x_2257_);
    return v_res_2261_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___redArg(
    mut v_x_2262_: *mut leanh::LeanObject,
    mut v_x_2263_: *mut leanh::LeanObject,
    mut v_m_2264_: *mut leanh::LeanObject,
    mut v_a_2265_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2266_: u8 = 0;
    v___x_2266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2262_, v_x_2263_, v_m_2264_, v_a_2265_,
    );
    return v___x_2266_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___redArg___boxed(
    mut v_x_2267_: *mut leanh::LeanObject,
    mut v_x_2268_: *mut leanh::LeanObject,
    mut v_m_2269_: *mut leanh::LeanObject,
    mut v_a_2270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2271_: u8 = 0;
    let mut v_r_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2271_ =
        l_Std_ExtDHashMap_instDecidableMem___redArg(v_x_2267_, v_x_2268_, v_m_2269_, v_a_2270_);
    leanh::lean_dec(v_m_2269_);
    v_r_2272_ = leanh::lean_box((v_res_2271_) as usize);
    return v_r_2272_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem(
    mut v_00_u03b1_2273_: *mut leanh::LeanObject,
    mut v_00_u03b2_2274_: *mut leanh::LeanObject,
    mut v_x_2275_: *mut leanh::LeanObject,
    mut v_x_2276_: *mut leanh::LeanObject,
    mut v_inst_2277_: *mut leanh::LeanObject,
    mut v_inst_2278_: *mut leanh::LeanObject,
    mut v_m_2279_: *mut leanh::LeanObject,
    mut v_a_2280_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2281_: u8 = 0;
    v___x_2281_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2275_, v_x_2276_, v_m_2279_, v_a_2280_,
    );
    return v___x_2281_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___boxed(
    mut v_00_u03b1_2282_: *mut leanh::LeanObject,
    mut v_00_u03b2_2283_: *mut leanh::LeanObject,
    mut v_x_2284_: *mut leanh::LeanObject,
    mut v_x_2285_: *mut leanh::LeanObject,
    mut v_inst_2286_: *mut leanh::LeanObject,
    mut v_inst_2287_: *mut leanh::LeanObject,
    mut v_m_2288_: *mut leanh::LeanObject,
    mut v_a_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2290_: u8 = 0;
    let mut v_r_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2288_);
    v_r_2291_ = leanh::lean_box((v_res_2290_) as usize);
    return v_r_2291_;
}
pub unsafe fn l_Std_ExtDHashMap_get___redArg(
    mut v_x_2292_: *mut leanh::LeanObject,
    mut v_x_2293_: *mut leanh::LeanObject,
    mut v_m_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ =
        l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_2292_, v_x_2293_, v_m_2294_, v_a_2295_);
    return v___x_2296_;
}
pub unsafe fn l_Std_ExtDHashMap_get___redArg___boxed(
    mut v_x_2297_: *mut leanh::LeanObject,
    mut v_x_2298_: *mut leanh::LeanObject,
    mut v_m_2299_: *mut leanh::LeanObject,
    mut v_a_2300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Std_ExtDHashMap_get___redArg(v_x_2297_, v_x_2298_, v_m_2299_, v_a_2300_);
    leanh::lean_dec(v_m_2299_);
    return v_res_2301_;
}
pub unsafe fn l_Std_ExtDHashMap_get(
    mut v_00_u03b1_2302_: *mut leanh::LeanObject,
    mut v_00_u03b2_2303_: *mut leanh::LeanObject,
    mut v_x_2304_: *mut leanh::LeanObject,
    mut v_x_2305_: *mut leanh::LeanObject,
    mut v_inst_2306_: *mut leanh::LeanObject,
    mut v_m_2307_: *mut leanh::LeanObject,
    mut v_a_2308_: *mut leanh::LeanObject,
    mut v_h_2309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ =
        l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_2304_, v_x_2305_, v_m_2307_, v_a_2308_);
    return v___x_2310_;
}
pub unsafe fn l_Std_ExtDHashMap_get___boxed(
    mut v_00_u03b1_2311_: *mut leanh::LeanObject,
    mut v_00_u03b2_2312_: *mut leanh::LeanObject,
    mut v_x_2313_: *mut leanh::LeanObject,
    mut v_x_2314_: *mut leanh::LeanObject,
    mut v_inst_2315_: *mut leanh::LeanObject,
    mut v_m_2316_: *mut leanh::LeanObject,
    mut v_a_2317_: *mut leanh::LeanObject,
    mut v_h_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2316_);
    return v_res_2319_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x21___redArg(
    mut v_x_2320_: *mut leanh::LeanObject,
    mut v_x_2321_: *mut leanh::LeanObject,
    mut v_m_2322_: *mut leanh::LeanObject,
    mut v_a_2323_: *mut leanh::LeanObject,
    mut v_inst_2324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2326_: *mut leanh::LeanObject,
    mut v_x_2327_: *mut leanh::LeanObject,
    mut v_m_2328_: *mut leanh::LeanObject,
    mut v_a_2329_: *mut leanh::LeanObject,
    mut v_inst_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Std_ExtDHashMap_get_x21___redArg(
        v_x_2326_,
        v_x_2327_,
        v_m_2328_,
        v_a_2329_,
        v_inst_2330_,
    );
    leanh::lean_dec(v_inst_2330_);
    leanh::lean_dec(v_m_2328_);
    return v_res_2331_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x21(
    mut v_00_u03b1_2332_: *mut leanh::LeanObject,
    mut v_00_u03b2_2333_: *mut leanh::LeanObject,
    mut v_x_2334_: *mut leanh::LeanObject,
    mut v_x_2335_: *mut leanh::LeanObject,
    mut v_inst_2336_: *mut leanh::LeanObject,
    mut v_m_2337_: *mut leanh::LeanObject,
    mut v_a_2338_: *mut leanh::LeanObject,
    mut v_inst_2339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2341_: *mut leanh::LeanObject,
    mut v_00_u03b2_2342_: *mut leanh::LeanObject,
    mut v_x_2343_: *mut leanh::LeanObject,
    mut v_x_2344_: *mut leanh::LeanObject,
    mut v_inst_2345_: *mut leanh::LeanObject,
    mut v_m_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
    mut v_inst_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_inst_2348_);
    leanh::lean_dec(v_m_2346_);
    return v_res_2349_;
}
pub unsafe fn l_Std_ExtDHashMap_getD___redArg(
    mut v_x_2350_: *mut leanh::LeanObject,
    mut v_x_2351_: *mut leanh::LeanObject,
    mut v_m_2352_: *mut leanh::LeanObject,
    mut v_a_2353_: *mut leanh::LeanObject,
    mut v_fallback_2354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2356_: *mut leanh::LeanObject,
    mut v_x_2357_: *mut leanh::LeanObject,
    mut v_m_2358_: *mut leanh::LeanObject,
    mut v_a_2359_: *mut leanh::LeanObject,
    mut v_fallback_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2361_ = l_Std_ExtDHashMap_getD___redArg(
        v_x_2356_,
        v_x_2357_,
        v_m_2358_,
        v_a_2359_,
        v_fallback_2360_,
    );
    leanh::lean_dec(v_fallback_2360_);
    leanh::lean_dec(v_m_2358_);
    return v_res_2361_;
}
pub unsafe fn l_Std_ExtDHashMap_getD(
    mut v_00_u03b1_2362_: *mut leanh::LeanObject,
    mut v_00_u03b2_2363_: *mut leanh::LeanObject,
    mut v_x_2364_: *mut leanh::LeanObject,
    mut v_x_2365_: *mut leanh::LeanObject,
    mut v_inst_2366_: *mut leanh::LeanObject,
    mut v_m_2367_: *mut leanh::LeanObject,
    mut v_a_2368_: *mut leanh::LeanObject,
    mut v_fallback_2369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2371_: *mut leanh::LeanObject,
    mut v_00_u03b2_2372_: *mut leanh::LeanObject,
    mut v_x_2373_: *mut leanh::LeanObject,
    mut v_x_2374_: *mut leanh::LeanObject,
    mut v_inst_2375_: *mut leanh::LeanObject,
    mut v_m_2376_: *mut leanh::LeanObject,
    mut v_a_2377_: *mut leanh::LeanObject,
    mut v_fallback_2378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_fallback_2378_);
    leanh::lean_dec(v_m_2376_);
    return v_res_2379_;
}
pub unsafe fn l_Std_ExtDHashMap_erase___redArg(
    mut v_x_2380_: *mut leanh::LeanObject,
    mut v_x_2381_: *mut leanh::LeanObject,
    mut v_m_2382_: *mut leanh::LeanObject,
    mut v_a_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_2380_, v_x_2381_, v_m_2382_, v_a_2383_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Std_ExtDHashMap_erase(
    mut v_00_u03b1_2385_: *mut leanh::LeanObject,
    mut v_00_u03b2_2386_: *mut leanh::LeanObject,
    mut v_x_2387_: *mut leanh::LeanObject,
    mut v_x_2388_: *mut leanh::LeanObject,
    mut v_inst_2389_: *mut leanh::LeanObject,
    mut v_inst_2390_: *mut leanh::LeanObject,
    mut v_m_2391_: *mut leanh::LeanObject,
    mut v_a_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_2387_, v_x_2388_, v_m_2391_, v_a_2392_,
    );
    return v___x_2393_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___redArg(
    mut v_x_2394_: *mut leanh::LeanObject,
    mut v_x_2395_: *mut leanh::LeanObject,
    mut v_m_2396_: *mut leanh::LeanObject,
    mut v_a_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2398_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_2394_, v_x_2395_, v_m_2396_, v_a_2397_,
    );
    return v___x_2398_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___redArg___boxed(
    mut v_x_2399_: *mut leanh::LeanObject,
    mut v_x_2400_: *mut leanh::LeanObject,
    mut v_m_2401_: *mut leanh::LeanObject,
    mut v_a_2402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2403_ =
        l_Std_ExtDHashMap_Const_get_x3f___redArg(v_x_2399_, v_x_2400_, v_m_2401_, v_a_2402_);
    leanh::lean_dec(v_m_2401_);
    return v_res_2403_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f(
    mut v_00_u03b1_2404_: *mut leanh::LeanObject,
    mut v_x_2405_: *mut leanh::LeanObject,
    mut v_x_2406_: *mut leanh::LeanObject,
    mut v_00_u03b2_2407_: *mut leanh::LeanObject,
    mut v_inst_2408_: *mut leanh::LeanObject,
    mut v_inst_2409_: *mut leanh::LeanObject,
    mut v_m_2410_: *mut leanh::LeanObject,
    mut v_a_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_2405_, v_x_2406_, v_m_2410_, v_a_2411_,
    );
    return v___x_2412_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___boxed(
    mut v_00_u03b1_2413_: *mut leanh::LeanObject,
    mut v_x_2414_: *mut leanh::LeanObject,
    mut v_x_2415_: *mut leanh::LeanObject,
    mut v_00_u03b2_2416_: *mut leanh::LeanObject,
    mut v_inst_2417_: *mut leanh::LeanObject,
    mut v_inst_2418_: *mut leanh::LeanObject,
    mut v_m_2419_: *mut leanh::LeanObject,
    mut v_a_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2419_);
    return v_res_2421_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___redArg(
    mut v_x_2422_: *mut leanh::LeanObject,
    mut v_x_2423_: *mut leanh::LeanObject,
    mut v_m_2424_: *mut leanh::LeanObject,
    mut v_a_2425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_2422_, v_x_2423_, v_m_2424_, v_a_2425_,
    );
    return v___x_2426_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___redArg___boxed(
    mut v_x_2427_: *mut leanh::LeanObject,
    mut v_x_2428_: *mut leanh::LeanObject,
    mut v_m_2429_: *mut leanh::LeanObject,
    mut v_a_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Std_ExtDHashMap_Const_get___redArg(v_x_2427_, v_x_2428_, v_m_2429_, v_a_2430_);
    leanh::lean_dec(v_m_2429_);
    return v_res_2431_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get(
    mut v_00_u03b1_2432_: *mut leanh::LeanObject,
    mut v_x_2433_: *mut leanh::LeanObject,
    mut v_x_2434_: *mut leanh::LeanObject,
    mut v_00_u03b2_2435_: *mut leanh::LeanObject,
    mut v_inst_2436_: *mut leanh::LeanObject,
    mut v_inst_2437_: *mut leanh::LeanObject,
    mut v_m_2438_: *mut leanh::LeanObject,
    mut v_a_2439_: *mut leanh::LeanObject,
    mut v_h_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_2433_, v_x_2434_, v_m_2438_, v_a_2439_,
    );
    return v___x_2441_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___boxed(
    mut v_00_u03b1_2442_: *mut leanh::LeanObject,
    mut v_x_2443_: *mut leanh::LeanObject,
    mut v_x_2444_: *mut leanh::LeanObject,
    mut v_00_u03b2_2445_: *mut leanh::LeanObject,
    mut v_inst_2446_: *mut leanh::LeanObject,
    mut v_inst_2447_: *mut leanh::LeanObject,
    mut v_m_2448_: *mut leanh::LeanObject,
    mut v_a_2449_: *mut leanh::LeanObject,
    mut v_h_2450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2448_);
    return v_res_2451_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getD___redArg(
    mut v_x_2452_: *mut leanh::LeanObject,
    mut v_x_2453_: *mut leanh::LeanObject,
    mut v_m_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_fallback_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2458_: *mut leanh::LeanObject,
    mut v_x_2459_: *mut leanh::LeanObject,
    mut v_m_2460_: *mut leanh::LeanObject,
    mut v_a_2461_: *mut leanh::LeanObject,
    mut v_fallback_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2463_ = l_Std_ExtDHashMap_Const_getD___redArg(
        v_x_2458_,
        v_x_2459_,
        v_m_2460_,
        v_a_2461_,
        v_fallback_2462_,
    );
    leanh::lean_dec(v_fallback_2462_);
    leanh::lean_dec(v_m_2460_);
    return v_res_2463_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getD(
    mut v_00_u03b1_2464_: *mut leanh::LeanObject,
    mut v_x_2465_: *mut leanh::LeanObject,
    mut v_x_2466_: *mut leanh::LeanObject,
    mut v_00_u03b2_2467_: *mut leanh::LeanObject,
    mut v_inst_2468_: *mut leanh::LeanObject,
    mut v_inst_2469_: *mut leanh::LeanObject,
    mut v_m_2470_: *mut leanh::LeanObject,
    mut v_a_2471_: *mut leanh::LeanObject,
    mut v_fallback_2472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2474_: *mut leanh::LeanObject,
    mut v_x_2475_: *mut leanh::LeanObject,
    mut v_x_2476_: *mut leanh::LeanObject,
    mut v_00_u03b2_2477_: *mut leanh::LeanObject,
    mut v_inst_2478_: *mut leanh::LeanObject,
    mut v_inst_2479_: *mut leanh::LeanObject,
    mut v_m_2480_: *mut leanh::LeanObject,
    mut v_a_2481_: *mut leanh::LeanObject,
    mut v_fallback_2482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_fallback_2482_);
    leanh::lean_dec(v_m_2480_);
    return v_res_2483_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x21___redArg(
    mut v_x_2484_: *mut leanh::LeanObject,
    mut v_x_2485_: *mut leanh::LeanObject,
    mut v_inst_2486_: *mut leanh::LeanObject,
    mut v_m_2487_: *mut leanh::LeanObject,
    mut v_a_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2490_: *mut leanh::LeanObject,
    mut v_x_2491_: *mut leanh::LeanObject,
    mut v_inst_2492_: *mut leanh::LeanObject,
    mut v_m_2493_: *mut leanh::LeanObject,
    mut v_a_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_Std_ExtDHashMap_Const_get_x21___redArg(
        v_x_2490_,
        v_x_2491_,
        v_inst_2492_,
        v_m_2493_,
        v_a_2494_,
    );
    leanh::lean_dec(v_m_2493_);
    leanh::lean_dec(v_inst_2492_);
    return v_res_2495_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x21(
    mut v_00_u03b1_2496_: *mut leanh::LeanObject,
    mut v_x_2497_: *mut leanh::LeanObject,
    mut v_x_2498_: *mut leanh::LeanObject,
    mut v_00_u03b2_2499_: *mut leanh::LeanObject,
    mut v_inst_2500_: *mut leanh::LeanObject,
    mut v_inst_2501_: *mut leanh::LeanObject,
    mut v_inst_2502_: *mut leanh::LeanObject,
    mut v_m_2503_: *mut leanh::LeanObject,
    mut v_a_2504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2506_: *mut leanh::LeanObject,
    mut v_x_2507_: *mut leanh::LeanObject,
    mut v_x_2508_: *mut leanh::LeanObject,
    mut v_00_u03b2_2509_: *mut leanh::LeanObject,
    mut v_inst_2510_: *mut leanh::LeanObject,
    mut v_inst_2511_: *mut leanh::LeanObject,
    mut v_inst_2512_: *mut leanh::LeanObject,
    mut v_m_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2513_);
    leanh::lean_dec(v_inst_2512_);
    return v_res_2515_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f___redArg(
    mut v_x_2516_: *mut leanh::LeanObject,
    mut v_x_2517_: *mut leanh::LeanObject,
    mut v_m_2518_: *mut leanh::LeanObject,
    mut v_a_2519_: *mut leanh::LeanObject,
    mut v_b_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v_val_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2562_: u8 = 0;
    let mut v_unused_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2521_ = leanh::lean_ctor_get(v_m_2518_, 0);
                v_buckets_2522_ = leanh::lean_ctor_get(v_m_2518_, 1);
                v___x_2523_ = lean_array_get_size(v_buckets_2522_);
                leanh::lean_inc_ref(v_x_2517_);
                leanh::lean_inc_n(v_a_2519_, 2);
                v___x_2524_ = leanh::lean_apply_1(v_x_2517_, v_a_2519_);
                v___x_2525_ = 32u64;
                v___x_2526_ = leanh::lean_unbox_uint64(v___x_2524_);
                v___x_2527_ = lean_uint64_shift_right(v___x_2526_, v___x_2525_);
                v___x_2528_ = leanh::lean_unbox_uint64(v___x_2524_);
                leanh::lean_dec_ref(v___x_2524_);
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
                leanh::lean_inc(v_bkt_2538_);
                v___x_2539_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_2516_,
                    v_a_2519_,
                    v_bkt_2538_,
                );
                if leanh::lean_obj_tag(v___x_2539_) == 0 {
                    leanh::lean_inc_ref(v_buckets_2522_);
                    leanh::lean_inc(v_size_2521_);
                    v_isSharedCheck_2562_ = (!leanh::lean_is_exclusive(v_m_2518_)) as u8;
                    if v_isSharedCheck_2562_ == 0 {
                        v_unused_2563_ = leanh::lean_ctor_get(v_m_2518_, 1);
                        leanh::lean_dec(v_unused_2563_);
                        v_unused_2564_ = leanh::lean_ctor_get(v_m_2518_, 0);
                        leanh::lean_dec(v_unused_2564_);
                        v___x_2541_ = v_m_2518_;
                        v_isShared_2542_ = v_isSharedCheck_2562_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2518_);
                        v___x_2541_ = leanh::lean_box(0);
                        v_isShared_2542_ = v_isSharedCheck_2562_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2520_);
                    leanh::lean_dec(v_a_2519_);
                    leanh::lean_dec_ref(v_x_2517_);
                    v___x_2565_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2565_, 0, v___x_2539_);
                    leanh::lean_ctor_set(v___x_2565_, 1, v_m_2518_);
                    return v___x_2565_;
                }
            }
            1 => {
                v___x_2543_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2544_ = lean_nat_add(v_size_2521_, v___x_2543_);
                leanh::lean_dec(v_size_2521_);
                leanh::lean_inc(v_bkt_2538_);
                v___x_2545_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2545_, 0, v_a_2519_);
                leanh::lean_ctor_set(v___x_2545_, 1, v_b_2520_);
                leanh::lean_ctor_set(v___x_2545_, 2, v_bkt_2538_);
                v_buckets_x27_2546_ = lean_array_uset(v_buckets_2522_, v___x_2537_, v___x_2545_);
                v___x_2547_ = leanh::lean_unsigned_to_nat(4);
                v___x_2548_ = lean_nat_mul(v_size_x27_2544_, v___x_2547_);
                v___x_2549_ = leanh::lean_unsigned_to_nat(3);
                v___x_2550_ = lean_nat_div(v___x_2548_, v___x_2549_);
                leanh::lean_dec(v___x_2548_);
                v___x_2551_ = lean_array_get_size(v_buckets_x27_2546_);
                v___x_2552_ = lean_nat_dec_le(v___x_2550_, v___x_2551_);
                leanh::lean_dec(v___x_2550_);
                if v___x_2552_ == 0 {
                    v_val_2553_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2517_,
                        v_buckets_x27_2546_,
                    );
                    if v_isShared_2542_ == 0 {
                        leanh::lean_ctor_set(v___x_2541_, 1, v_val_2553_);
                        leanh::lean_ctor_set(v___x_2541_, 0, v_size_x27_2544_);
                        v___x_2555_ = v___x_2541_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2557_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_size_x27_2544_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_val_2553_);
                        v___x_2555_ = v_reuseFailAlloc_2557_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2517_);
                    if v_isShared_2542_ == 0 {
                        leanh::lean_ctor_set(v___x_2541_, 1, v_buckets_x27_2546_);
                        leanh::lean_ctor_set(v___x_2541_, 0, v_size_x27_2544_);
                        v___x_2559_ = v___x_2541_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_size_x27_2544_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_buckets_x27_2546_);
                        v___x_2559_ = v_reuseFailAlloc_2561_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2556_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2556_, 0, v___x_2539_);
                leanh::lean_ctor_set(v___x_2556_, 1, v___x_2555_);
                return v___x_2556_;
            }
            3 => {
                v___x_2560_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2560_, 0, v___x_2539_);
                leanh::lean_ctor_set(v___x_2560_, 1, v___x_2559_);
                return v___x_2560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2566_: *mut leanh::LeanObject,
    mut v_x_2567_: *mut leanh::LeanObject,
    mut v_x_2568_: *mut leanh::LeanObject,
    mut v_00_u03b2_2569_: *mut leanh::LeanObject,
    mut v_inst_2570_: *mut leanh::LeanObject,
    mut v_inst_2571_: *mut leanh::LeanObject,
    mut v_m_2572_: *mut leanh::LeanObject,
    mut v_a_2573_: *mut leanh::LeanObject,
    mut v_b_2574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut v_val_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_unused_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2575_ = leanh::lean_ctor_get(v_m_2572_, 0);
                v_buckets_2576_ = leanh::lean_ctor_get(v_m_2572_, 1);
                v___x_2577_ = lean_array_get_size(v_buckets_2576_);
                leanh::lean_inc_ref(v_x_2568_);
                leanh::lean_inc_n(v_a_2573_, 2);
                v___x_2578_ = leanh::lean_apply_1(v_x_2568_, v_a_2573_);
                v___x_2579_ = 32u64;
                v___x_2580_ = leanh::lean_unbox_uint64(v___x_2578_);
                v___x_2581_ = lean_uint64_shift_right(v___x_2580_, v___x_2579_);
                v___x_2582_ = leanh::lean_unbox_uint64(v___x_2578_);
                leanh::lean_dec_ref(v___x_2578_);
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
                leanh::lean_inc(v_bkt_2592_);
                v___x_2593_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_2567_,
                    v_a_2573_,
                    v_bkt_2592_,
                );
                if leanh::lean_obj_tag(v___x_2593_) == 0 {
                    leanh::lean_inc_ref(v_buckets_2576_);
                    leanh::lean_inc(v_size_2575_);
                    v_isSharedCheck_2616_ = (!leanh::lean_is_exclusive(v_m_2572_)) as u8;
                    if v_isSharedCheck_2616_ == 0 {
                        v_unused_2617_ = leanh::lean_ctor_get(v_m_2572_, 1);
                        leanh::lean_dec(v_unused_2617_);
                        v_unused_2618_ = leanh::lean_ctor_get(v_m_2572_, 0);
                        leanh::lean_dec(v_unused_2618_);
                        v___x_2595_ = v_m_2572_;
                        v_isShared_2596_ = v_isSharedCheck_2616_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2572_);
                        v___x_2595_ = leanh::lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2616_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2574_);
                    leanh::lean_dec(v_a_2573_);
                    leanh::lean_dec_ref(v_x_2568_);
                    v___x_2619_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2619_, 0, v___x_2593_);
                    leanh::lean_ctor_set(v___x_2619_, 1, v_m_2572_);
                    return v___x_2619_;
                }
            }
            1 => {
                v___x_2597_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2598_ = lean_nat_add(v_size_2575_, v___x_2597_);
                leanh::lean_dec(v_size_2575_);
                leanh::lean_inc(v_bkt_2592_);
                v___x_2599_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2599_, 0, v_a_2573_);
                leanh::lean_ctor_set(v___x_2599_, 1, v_b_2574_);
                leanh::lean_ctor_set(v___x_2599_, 2, v_bkt_2592_);
                v_buckets_x27_2600_ = lean_array_uset(v_buckets_2576_, v___x_2591_, v___x_2599_);
                v___x_2601_ = leanh::lean_unsigned_to_nat(4);
                v___x_2602_ = lean_nat_mul(v_size_x27_2598_, v___x_2601_);
                v___x_2603_ = leanh::lean_unsigned_to_nat(3);
                v___x_2604_ = lean_nat_div(v___x_2602_, v___x_2603_);
                leanh::lean_dec(v___x_2602_);
                v___x_2605_ = lean_array_get_size(v_buckets_x27_2600_);
                v___x_2606_ = lean_nat_dec_le(v___x_2604_, v___x_2605_);
                leanh::lean_dec(v___x_2604_);
                if v___x_2606_ == 0 {
                    v_val_2607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2568_,
                        v_buckets_x27_2600_,
                    );
                    if v_isShared_2596_ == 0 {
                        leanh::lean_ctor_set(v___x_2595_, 1, v_val_2607_);
                        leanh::lean_ctor_set(v___x_2595_, 0, v_size_x27_2598_);
                        v___x_2609_ = v___x_2595_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2611_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_size_x27_2598_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_val_2607_);
                        v___x_2609_ = v_reuseFailAlloc_2611_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2568_);
                    if v_isShared_2596_ == 0 {
                        leanh::lean_ctor_set(v___x_2595_, 1, v_buckets_x27_2600_);
                        leanh::lean_ctor_set(v___x_2595_, 0, v_size_x27_2598_);
                        v___x_2613_ = v___x_2595_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2615_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_size_x27_2598_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_buckets_x27_2600_);
                        v___x_2613_ = v_reuseFailAlloc_2615_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2610_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2610_, 0, v___x_2593_);
                leanh::lean_ctor_set(v___x_2610_, 1, v___x_2609_);
                return v___x_2610_;
            }
            3 => {
                v___x_2614_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2614_, 0, v___x_2593_);
                leanh::lean_ctor_set(v___x_2614_, 1, v___x_2613_);
                return v___x_2614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___redArg(
    mut v_x_2620_: *mut leanh::LeanObject,
    mut v_x_2621_: *mut leanh::LeanObject,
    mut v_m_2622_: *mut leanh::LeanObject,
    mut v_a_2623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2624_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_2620_, v_x_2621_, v_m_2622_, v_a_2623_,
    );
    return v___x_2624_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___redArg___boxed(
    mut v_x_2625_: *mut leanh::LeanObject,
    mut v_x_2626_: *mut leanh::LeanObject,
    mut v_m_2627_: *mut leanh::LeanObject,
    mut v_a_2628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2629_ = l_Std_ExtDHashMap_getKey_x3f___redArg(v_x_2625_, v_x_2626_, v_m_2627_, v_a_2628_);
    leanh::lean_dec(v_m_2627_);
    return v_res_2629_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f(
    mut v_00_u03b1_2630_: *mut leanh::LeanObject,
    mut v_00_u03b2_2631_: *mut leanh::LeanObject,
    mut v_x_2632_: *mut leanh::LeanObject,
    mut v_x_2633_: *mut leanh::LeanObject,
    mut v_inst_2634_: *mut leanh::LeanObject,
    mut v_inst_2635_: *mut leanh::LeanObject,
    mut v_m_2636_: *mut leanh::LeanObject,
    mut v_a_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_2632_, v_x_2633_, v_m_2636_, v_a_2637_,
    );
    return v___x_2638_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___boxed(
    mut v_00_u03b1_2639_: *mut leanh::LeanObject,
    mut v_00_u03b2_2640_: *mut leanh::LeanObject,
    mut v_x_2641_: *mut leanh::LeanObject,
    mut v_x_2642_: *mut leanh::LeanObject,
    mut v_inst_2643_: *mut leanh::LeanObject,
    mut v_inst_2644_: *mut leanh::LeanObject,
    mut v_m_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2645_);
    return v_res_2647_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___redArg(
    mut v_x_2648_: *mut leanh::LeanObject,
    mut v_x_2649_: *mut leanh::LeanObject,
    mut v_m_2650_: *mut leanh::LeanObject,
    mut v_a_2651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_2648_, v_x_2649_, v_m_2650_, v_a_2651_,
    );
    return v___x_2652_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___redArg___boxed(
    mut v_x_2653_: *mut leanh::LeanObject,
    mut v_x_2654_: *mut leanh::LeanObject,
    mut v_m_2655_: *mut leanh::LeanObject,
    mut v_a_2656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Std_ExtDHashMap_getKey___redArg(v_x_2653_, v_x_2654_, v_m_2655_, v_a_2656_);
    leanh::lean_dec(v_m_2655_);
    return v_res_2657_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey(
    mut v_00_u03b1_2658_: *mut leanh::LeanObject,
    mut v_00_u03b2_2659_: *mut leanh::LeanObject,
    mut v_x_2660_: *mut leanh::LeanObject,
    mut v_x_2661_: *mut leanh::LeanObject,
    mut v_inst_2662_: *mut leanh::LeanObject,
    mut v_inst_2663_: *mut leanh::LeanObject,
    mut v_m_2664_: *mut leanh::LeanObject,
    mut v_a_2665_: *mut leanh::LeanObject,
    mut v_h_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_2660_, v_x_2661_, v_m_2664_, v_a_2665_,
    );
    return v___x_2667_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___boxed(
    mut v_00_u03b1_2668_: *mut leanh::LeanObject,
    mut v_00_u03b2_2669_: *mut leanh::LeanObject,
    mut v_x_2670_: *mut leanh::LeanObject,
    mut v_x_2671_: *mut leanh::LeanObject,
    mut v_inst_2672_: *mut leanh::LeanObject,
    mut v_inst_2673_: *mut leanh::LeanObject,
    mut v_m_2674_: *mut leanh::LeanObject,
    mut v_a_2675_: *mut leanh::LeanObject,
    mut v_h_2676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2674_);
    return v_res_2677_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x21___redArg(
    mut v_x_2678_: *mut leanh::LeanObject,
    mut v_x_2679_: *mut leanh::LeanObject,
    mut v_inst_2680_: *mut leanh::LeanObject,
    mut v_m_2681_: *mut leanh::LeanObject,
    mut v_a_2682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2684_: *mut leanh::LeanObject,
    mut v_x_2685_: *mut leanh::LeanObject,
    mut v_inst_2686_: *mut leanh::LeanObject,
    mut v_m_2687_: *mut leanh::LeanObject,
    mut v_a_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Std_ExtDHashMap_getKey_x21___redArg(
        v_x_2684_,
        v_x_2685_,
        v_inst_2686_,
        v_m_2687_,
        v_a_2688_,
    );
    leanh::lean_dec(v_m_2687_);
    leanh::lean_dec(v_inst_2686_);
    return v_res_2689_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x21(
    mut v_00_u03b1_2690_: *mut leanh::LeanObject,
    mut v_00_u03b2_2691_: *mut leanh::LeanObject,
    mut v_x_2692_: *mut leanh::LeanObject,
    mut v_x_2693_: *mut leanh::LeanObject,
    mut v_inst_2694_: *mut leanh::LeanObject,
    mut v_inst_2695_: *mut leanh::LeanObject,
    mut v_inst_2696_: *mut leanh::LeanObject,
    mut v_m_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2700_: *mut leanh::LeanObject,
    mut v_00_u03b2_2701_: *mut leanh::LeanObject,
    mut v_x_2702_: *mut leanh::LeanObject,
    mut v_x_2703_: *mut leanh::LeanObject,
    mut v_inst_2704_: *mut leanh::LeanObject,
    mut v_inst_2705_: *mut leanh::LeanObject,
    mut v_inst_2706_: *mut leanh::LeanObject,
    mut v_m_2707_: *mut leanh::LeanObject,
    mut v_a_2708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_m_2707_);
    leanh::lean_dec(v_inst_2706_);
    return v_res_2709_;
}
pub unsafe fn l_Std_ExtDHashMap_getKeyD___redArg(
    mut v_x_2710_: *mut leanh::LeanObject,
    mut v_x_2711_: *mut leanh::LeanObject,
    mut v_m_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v_fallback_2714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2716_: *mut leanh::LeanObject,
    mut v_x_2717_: *mut leanh::LeanObject,
    mut v_m_2718_: *mut leanh::LeanObject,
    mut v_a_2719_: *mut leanh::LeanObject,
    mut v_fallback_2720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_Std_ExtDHashMap_getKeyD___redArg(
        v_x_2716_,
        v_x_2717_,
        v_m_2718_,
        v_a_2719_,
        v_fallback_2720_,
    );
    leanh::lean_dec(v_fallback_2720_);
    leanh::lean_dec(v_m_2718_);
    return v_res_2721_;
}
pub unsafe fn l_Std_ExtDHashMap_getKeyD(
    mut v_00_u03b1_2722_: *mut leanh::LeanObject,
    mut v_00_u03b2_2723_: *mut leanh::LeanObject,
    mut v_x_2724_: *mut leanh::LeanObject,
    mut v_x_2725_: *mut leanh::LeanObject,
    mut v_inst_2726_: *mut leanh::LeanObject,
    mut v_inst_2727_: *mut leanh::LeanObject,
    mut v_m_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
    mut v_fallback_2730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2732_: *mut leanh::LeanObject,
    mut v_00_u03b2_2733_: *mut leanh::LeanObject,
    mut v_x_2734_: *mut leanh::LeanObject,
    mut v_x_2735_: *mut leanh::LeanObject,
    mut v_inst_2736_: *mut leanh::LeanObject,
    mut v_inst_2737_: *mut leanh::LeanObject,
    mut v_m_2738_: *mut leanh::LeanObject,
    mut v_a_2739_: *mut leanh::LeanObject,
    mut v_fallback_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_fallback_2740_);
    leanh::lean_dec(v_m_2738_);
    return v_res_2741_;
}
pub unsafe fn l_Std_ExtDHashMap_size___redArg(
    mut v_m_2742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_2743_ = leanh::lean_ctor_get(v_m_2742_, 0);
    leanh::lean_inc(v_size_2743_);
    return v_size_2743_;
}
pub unsafe fn l_Std_ExtDHashMap_size___redArg___boxed(
    mut v_m_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2745_ = l_Std_ExtDHashMap_size___redArg(v_m_2744_);
    leanh::lean_dec(v_m_2744_);
    return v_res_2745_;
}
pub unsafe fn l_Std_ExtDHashMap_size(
    mut v_00_u03b1_2746_: *mut leanh::LeanObject,
    mut v_00_u03b2_2747_: *mut leanh::LeanObject,
    mut v_x_2748_: *mut leanh::LeanObject,
    mut v_x_2749_: *mut leanh::LeanObject,
    mut v_inst_2750_: *mut leanh::LeanObject,
    mut v_inst_2751_: *mut leanh::LeanObject,
    mut v_m_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_2753_ = leanh::lean_ctor_get(v_m_2752_, 0);
    leanh::lean_inc(v_size_2753_);
    return v_size_2753_;
}
pub unsafe fn l_Std_ExtDHashMap_size___boxed(
    mut v_00_u03b1_2754_: *mut leanh::LeanObject,
    mut v_00_u03b2_2755_: *mut leanh::LeanObject,
    mut v_x_2756_: *mut leanh::LeanObject,
    mut v_x_2757_: *mut leanh::LeanObject,
    mut v_inst_2758_: *mut leanh::LeanObject,
    mut v_inst_2759_: *mut leanh::LeanObject,
    mut v_m_2760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_Std_ExtDHashMap_size(
        v_00_u03b1_2754_,
        v_00_u03b2_2755_,
        v_x_2756_,
        v_x_2757_,
        v_inst_2758_,
        v_inst_2759_,
        v_m_2760_,
    );
    leanh::lean_dec(v_m_2760_);
    leanh::lean_dec_ref(v_x_2757_);
    leanh::lean_dec_ref(v_x_2756_);
    return v_res_2761_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___redArg(
    mut v_m_2762_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    v_size_2763_ = leanh::lean_ctor_get(v_m_2762_, 0);
    v___x_2764_ = leanh::lean_unsigned_to_nat(0);
    v___x_2765_ = lean_nat_dec_eq(v_size_2763_, v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___redArg___boxed(
    mut v_m_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2767_: u8 = 0;
    let mut v_r_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Std_ExtDHashMap_isEmpty___redArg(v_m_2766_);
    leanh::lean_dec(v_m_2766_);
    v_r_2768_ = leanh::lean_box((v_res_2767_) as usize);
    return v_r_2768_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty(
    mut v_00_u03b1_2769_: *mut leanh::LeanObject,
    mut v_00_u03b2_2770_: *mut leanh::LeanObject,
    mut v_x_2771_: *mut leanh::LeanObject,
    mut v_x_2772_: *mut leanh::LeanObject,
    mut v_inst_2773_: *mut leanh::LeanObject,
    mut v_inst_2774_: *mut leanh::LeanObject,
    mut v_m_2775_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    v_size_2776_ = leanh::lean_ctor_get(v_m_2775_, 0);
    v___x_2777_ = leanh::lean_unsigned_to_nat(0);
    v___x_2778_ = lean_nat_dec_eq(v_size_2776_, v___x_2777_);
    return v___x_2778_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___boxed(
    mut v_00_u03b1_2779_: *mut leanh::LeanObject,
    mut v_00_u03b2_2780_: *mut leanh::LeanObject,
    mut v_x_2781_: *mut leanh::LeanObject,
    mut v_x_2782_: *mut leanh::LeanObject,
    mut v_inst_2783_: *mut leanh::LeanObject,
    mut v_inst_2784_: *mut leanh::LeanObject,
    mut v_m_2785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2786_: u8 = 0;
    let mut v_r_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2786_ = l_Std_ExtDHashMap_isEmpty(
        v_00_u03b1_2779_,
        v_00_u03b2_2780_,
        v_x_2781_,
        v_x_2782_,
        v_inst_2783_,
        v_inst_2784_,
        v_m_2785_,
    );
    leanh::lean_dec(v_m_2785_);
    leanh::lean_dec_ref(v_x_2782_);
    leanh::lean_dec_ref(v_x_2781_);
    v_r_2787_ = leanh::lean_box((v_res_2786_) as usize);
    return v_r_2787_;
}
pub unsafe fn l_Std_ExtDHashMap_filter___redArg(
    mut v_f_2788_: *mut leanh::LeanObject,
    mut v_m_2789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2790_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2788_, v_m_2789_);
    return v___x_2790_;
}
pub unsafe fn l_Std_ExtDHashMap_filter(
    mut v_00_u03b1_2791_: *mut leanh::LeanObject,
    mut v_00_u03b2_2792_: *mut leanh::LeanObject,
    mut v_x_2793_: *mut leanh::LeanObject,
    mut v_x_2794_: *mut leanh::LeanObject,
    mut v_inst_2795_: *mut leanh::LeanObject,
    mut v_inst_2796_: *mut leanh::LeanObject,
    mut v_f_2797_: *mut leanh::LeanObject,
    mut v_m_2798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2799_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2797_, v_m_2798_);
    return v___x_2799_;
}
pub unsafe fn l_Std_ExtDHashMap_filter___boxed(
    mut v_00_u03b1_2800_: *mut leanh::LeanObject,
    mut v_00_u03b2_2801_: *mut leanh::LeanObject,
    mut v_x_2802_: *mut leanh::LeanObject,
    mut v_x_2803_: *mut leanh::LeanObject,
    mut v_inst_2804_: *mut leanh::LeanObject,
    mut v_inst_2805_: *mut leanh::LeanObject,
    mut v_f_2806_: *mut leanh::LeanObject,
    mut v_m_2807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_x_2803_);
    leanh::lean_dec_ref(v_x_2802_);
    return v_res_2808_;
}
pub unsafe fn l_Std_ExtDHashMap_map___redArg(
    mut v_f_2809_: *mut leanh::LeanObject,
    mut v_m_2810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2811_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2809_, v_m_2810_);
    return v___x_2811_;
}
pub unsafe fn l_Std_ExtDHashMap_map(
    mut v_00_u03b1_2812_: *mut leanh::LeanObject,
    mut v_00_u03b2_2813_: *mut leanh::LeanObject,
    mut v_00_u03b3_2814_: *mut leanh::LeanObject,
    mut v_x_2815_: *mut leanh::LeanObject,
    mut v_x_2816_: *mut leanh::LeanObject,
    mut v_inst_2817_: *mut leanh::LeanObject,
    mut v_inst_2818_: *mut leanh::LeanObject,
    mut v_f_2819_: *mut leanh::LeanObject,
    mut v_m_2820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2821_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2819_, v_m_2820_);
    return v___x_2821_;
}
pub unsafe fn l_Std_ExtDHashMap_map___boxed(
    mut v_00_u03b1_2822_: *mut leanh::LeanObject,
    mut v_00_u03b2_2823_: *mut leanh::LeanObject,
    mut v_00_u03b3_2824_: *mut leanh::LeanObject,
    mut v_x_2825_: *mut leanh::LeanObject,
    mut v_x_2826_: *mut leanh::LeanObject,
    mut v_inst_2827_: *mut leanh::LeanObject,
    mut v_inst_2828_: *mut leanh::LeanObject,
    mut v_f_2829_: *mut leanh::LeanObject,
    mut v_m_2830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_x_2826_);
    leanh::lean_dec_ref(v_x_2825_);
    return v_res_2831_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap___redArg(
    mut v_f_2832_: *mut leanh::LeanObject,
    mut v_m_2833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2834_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2832_, v_m_2833_);
    return v___x_2834_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap(
    mut v_00_u03b1_2835_: *mut leanh::LeanObject,
    mut v_00_u03b2_2836_: *mut leanh::LeanObject,
    mut v_00_u03b3_2837_: *mut leanh::LeanObject,
    mut v_x_2838_: *mut leanh::LeanObject,
    mut v_x_2839_: *mut leanh::LeanObject,
    mut v_inst_2840_: *mut leanh::LeanObject,
    mut v_inst_2841_: *mut leanh::LeanObject,
    mut v_f_2842_: *mut leanh::LeanObject,
    mut v_m_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2842_, v_m_2843_);
    return v___x_2844_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap___boxed(
    mut v_00_u03b1_2845_: *mut leanh::LeanObject,
    mut v_00_u03b2_2846_: *mut leanh::LeanObject,
    mut v_00_u03b3_2847_: *mut leanh::LeanObject,
    mut v_x_2848_: *mut leanh::LeanObject,
    mut v_x_2849_: *mut leanh::LeanObject,
    mut v_inst_2850_: *mut leanh::LeanObject,
    mut v_inst_2851_: *mut leanh::LeanObject,
    mut v_f_2852_: *mut leanh::LeanObject,
    mut v_m_2853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_x_2849_);
    leanh::lean_dec_ref(v_x_2848_);
    return v_res_2854_;
}
pub unsafe fn l_Std_ExtDHashMap_modify___redArg(
    mut v_x_2855_: *mut leanh::LeanObject,
    mut v_x_2856_: *mut leanh::LeanObject,
    mut v_m_2857_: *mut leanh::LeanObject,
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_f_2859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_x_2855_, v_x_2856_, v_m_2857_, v_a_2858_, v_f_2859_,
    );
    return v___x_2860_;
}
pub unsafe fn l_Std_ExtDHashMap_modify(
    mut v_00_u03b1_2861_: *mut leanh::LeanObject,
    mut v_00_u03b2_2862_: *mut leanh::LeanObject,
    mut v_x_2863_: *mut leanh::LeanObject,
    mut v_x_2864_: *mut leanh::LeanObject,
    mut v_inst_2865_: *mut leanh::LeanObject,
    mut v_m_2866_: *mut leanh::LeanObject,
    mut v_a_2867_: *mut leanh::LeanObject,
    mut v_f_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_x_2863_, v_x_2864_, v_m_2866_, v_a_2867_, v_f_2868_,
    );
    return v___x_2869_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_modify___redArg(
    mut v_x_2870_: *mut leanh::LeanObject,
    mut v_x_2871_: *mut leanh::LeanObject,
    mut v_m_2872_: *mut leanh::LeanObject,
    mut v_a_2873_: *mut leanh::LeanObject,
    mut v_f_2874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_2870_, v_x_2871_, v_m_2872_, v_a_2873_, v_f_2874_,
    );
    return v___x_2875_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_modify(
    mut v_00_u03b1_2876_: *mut leanh::LeanObject,
    mut v_x_2877_: *mut leanh::LeanObject,
    mut v_x_2878_: *mut leanh::LeanObject,
    mut v_inst_2879_: *mut leanh::LeanObject,
    mut v_inst_2880_: *mut leanh::LeanObject,
    mut v_00_u03b2_2881_: *mut leanh::LeanObject,
    mut v_m_2882_: *mut leanh::LeanObject,
    mut v_a_2883_: *mut leanh::LeanObject,
    mut v_f_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_2877_, v_x_2878_, v_m_2882_, v_a_2883_, v_f_2884_,
    );
    return v___x_2885_;
}
pub unsafe fn l_Std_ExtDHashMap_alter___redArg(
    mut v_x_2886_: *mut leanh::LeanObject,
    mut v_x_2887_: *mut leanh::LeanObject,
    mut v_m_2888_: *mut leanh::LeanObject,
    mut v_a_2889_: *mut leanh::LeanObject,
    mut v_f_2890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2891_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_x_2886_, v_x_2887_, v_m_2888_, v_a_2889_, v_f_2890_,
    );
    return v___x_2891_;
}
pub unsafe fn l_Std_ExtDHashMap_alter(
    mut v_00_u03b1_2892_: *mut leanh::LeanObject,
    mut v_00_u03b2_2893_: *mut leanh::LeanObject,
    mut v_x_2894_: *mut leanh::LeanObject,
    mut v_x_2895_: *mut leanh::LeanObject,
    mut v_inst_2896_: *mut leanh::LeanObject,
    mut v_m_2897_: *mut leanh::LeanObject,
    mut v_a_2898_: *mut leanh::LeanObject,
    mut v_f_2899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2900_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_x_2894_, v_x_2895_, v_m_2897_, v_a_2898_, v_f_2899_,
    );
    return v___x_2900_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_alter___redArg(
    mut v_x_2901_: *mut leanh::LeanObject,
    mut v_x_2902_: *mut leanh::LeanObject,
    mut v_m_2903_: *mut leanh::LeanObject,
    mut v_a_2904_: *mut leanh::LeanObject,
    mut v_f_2905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2906_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_2901_, v_x_2902_, v_m_2903_, v_a_2904_, v_f_2905_,
    );
    return v___x_2906_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_alter(
    mut v_00_u03b1_2907_: *mut leanh::LeanObject,
    mut v_x_2908_: *mut leanh::LeanObject,
    mut v_x_2909_: *mut leanh::LeanObject,
    mut v_inst_2910_: *mut leanh::LeanObject,
    mut v_inst_2911_: *mut leanh::LeanObject,
    mut v_00_u03b2_2912_: *mut leanh::LeanObject,
    mut v_m_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
    mut v_f_2915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_2908_, v_x_2909_, v_m_2913_, v_a_2914_, v_f_2915_,
    );
    return v___x_2916_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany___redArg___lam__0(
    mut v_x_2917_: *mut leanh::LeanObject,
    mut v_x_2918_: *mut leanh::LeanObject,
    mut v_x_2919_: *mut leanh::LeanObject,
    mut v_____s_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2921_ = leanh::lean_ctor_get(v_x_2919_, 0);
    leanh::lean_inc(v_fst_2921_);
    v_snd_2922_ = leanh::lean_ctor_get(v_x_2919_, 1);
    leanh::lean_inc(v_snd_2922_);
    leanh::lean_dec_ref(v_x_2919_);
    v_m_2923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2917_,
        v_x_2918_,
        v_____s_2920_,
        v_fst_2921_,
        v_snd_2922_,
    );
    v___x_2924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2924_, 0, v_m_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany___redArg(
    mut v_x_2925_: *mut leanh::LeanObject,
    mut v_x_2926_: *mut leanh::LeanObject,
    mut v_inst_2927_: *mut leanh::LeanObject,
    mut v_m_2928_: *mut leanh::LeanObject,
    mut v_l_2929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2930_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2930_, 0, v_x_2925_);
    leanh::lean_closure_set(v___f_2930_, 1, v_x_2926_);
    v___x_2931_ = leanh::lean_apply_4(
        v_inst_2927_,
        leanh::lean_box(0),
        v_l_2929_,
        v_m_2928_,
        v___f_2930_,
    );
    return v___x_2931_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany(
    mut v_00_u03b1_2932_: *mut leanh::LeanObject,
    mut v_00_u03b2_2933_: *mut leanh::LeanObject,
    mut v_x_2934_: *mut leanh::LeanObject,
    mut v_x_2935_: *mut leanh::LeanObject,
    mut v_inst_2936_: *mut leanh::LeanObject,
    mut v_inst_2937_: *mut leanh::LeanObject,
    mut v_00_u03c1_2938_: *mut leanh::LeanObject,
    mut v_inst_2939_: *mut leanh::LeanObject,
    mut v_m_2940_: *mut leanh::LeanObject,
    mut v_l_2941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2942_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2942_, 0, v_x_2934_);
    leanh::lean_closure_set(v___f_2942_, 1, v_x_2935_);
    v___x_2943_ = leanh::lean_apply_4(
        v_inst_2939_,
        leanh::lean_box(0),
        v_l_2941_,
        v_m_2940_,
        v___f_2942_,
    );
    return v___x_2943_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0(
    mut v_x_2944_: *mut leanh::LeanObject,
    mut v_x_2945_: *mut leanh::LeanObject,
    mut v_x_2946_: *mut leanh::LeanObject,
    mut v_____s_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2948_ = leanh::lean_ctor_get(v_x_2946_, 0);
    leanh::lean_inc(v_fst_2948_);
    v_snd_2949_ = leanh::lean_ctor_get(v_x_2946_, 1);
    leanh::lean_inc(v_snd_2949_);
    leanh::lean_dec_ref(v_x_2946_);
    v_m_2950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2944_,
        v_x_2945_,
        v_____s_2947_,
        v_fst_2948_,
        v_snd_2949_,
    );
    v___x_2951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2951_, 0, v_m_2950_);
    return v___x_2951_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany___redArg(
    mut v_x_2952_: *mut leanh::LeanObject,
    mut v_x_2953_: *mut leanh::LeanObject,
    mut v_inst_2954_: *mut leanh::LeanObject,
    mut v_m_2955_: *mut leanh::LeanObject,
    mut v_l_2956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2957_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2957_, 0, v_x_2952_);
    leanh::lean_closure_set(v___f_2957_, 1, v_x_2953_);
    v___x_2958_ = leanh::lean_apply_4(
        v_inst_2954_,
        leanh::lean_box(0),
        v_l_2956_,
        v_m_2955_,
        v___f_2957_,
    );
    return v___x_2958_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany(
    mut v_00_u03b1_2959_: *mut leanh::LeanObject,
    mut v_x_2960_: *mut leanh::LeanObject,
    mut v_x_2961_: *mut leanh::LeanObject,
    mut v_inst_2962_: *mut leanh::LeanObject,
    mut v_inst_2963_: *mut leanh::LeanObject,
    mut v_00_u03b2_2964_: *mut leanh::LeanObject,
    mut v_00_u03c1_2965_: *mut leanh::LeanObject,
    mut v_inst_2966_: *mut leanh::LeanObject,
    mut v_m_2967_: *mut leanh::LeanObject,
    mut v_l_2968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2969_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2969_, 0, v_x_2960_);
    leanh::lean_closure_set(v___f_2969_, 1, v_x_2961_);
    v___x_2970_ = leanh::lean_apply_4(
        v_inst_2966_,
        leanh::lean_box(0),
        v_l_2968_,
        v_m_2967_,
        v___f_2969_,
    );
    return v___x_2970_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0(
    mut v_x_2971_: *mut leanh::LeanObject,
    mut v_x_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
    mut v_____s_2974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = leanh::lean_box(0);
    v_m_2976_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2971_,
        v_x_2972_,
        v_____s_2974_,
        v_a_2973_,
        v___x_2975_,
    );
    v___x_2977_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2977_, 0, v_m_2976_);
    return v___x_2977_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg(
    mut v_x_2978_: *mut leanh::LeanObject,
    mut v_x_2979_: *mut leanh::LeanObject,
    mut v_inst_2980_: *mut leanh::LeanObject,
    mut v_m_2981_: *mut leanh::LeanObject,
    mut v_l_2982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2983_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2983_, 0, v_x_2978_);
    leanh::lean_closure_set(v___f_2983_, 1, v_x_2979_);
    v___x_2984_ = leanh::lean_apply_4(
        v_inst_2980_,
        leanh::lean_box(0),
        v_l_2982_,
        v_m_2981_,
        v___f_2983_,
    );
    return v___x_2984_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit(
    mut v_00_u03b1_2985_: *mut leanh::LeanObject,
    mut v_x_2986_: *mut leanh::LeanObject,
    mut v_x_2987_: *mut leanh::LeanObject,
    mut v_inst_2988_: *mut leanh::LeanObject,
    mut v_inst_2989_: *mut leanh::LeanObject,
    mut v_00_u03c1_2990_: *mut leanh::LeanObject,
    mut v_inst_2991_: *mut leanh::LeanObject,
    mut v_m_2992_: *mut leanh::LeanObject,
    mut v_l_2993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2994_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2994_, 0, v_x_2986_);
    leanh::lean_closure_set(v___f_2994_, 1, v_x_2987_);
    v___x_2995_ = leanh::lean_apply_4(
        v_inst_2991_,
        leanh::lean_box(0),
        v_l_2993_,
        v_m_2992_,
        v___f_2994_,
    );
    return v___x_2995_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg___lam__0(
    mut v_x_2996_: *mut leanh::LeanObject,
    mut v_x_2997_: *mut leanh::LeanObject,
    mut v_a_2998_: *mut leanh::LeanObject,
    mut v_b_2999_: *mut leanh::LeanObject,
    mut v_acc_3000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_3001_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2996_,
        v_x_2997_,
        v_acc_3000_,
        v_a_2998_,
        v_b_2999_,
    );
    v___x_3002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3002_, 0, v_r_3001_);
    return v___x_3002_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg___lam__1(
    mut v___x_3003_: *mut leanh::LeanObject,
    mut v___f_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
    mut v_x_3006_: *mut leanh::LeanObject,
    mut v___y_3007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3003_, v___f_3004_, v_a_3005_, v___y_3007_);
    return v___x_3008_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg(
    mut v_x_3030_: *mut leanh::LeanObject,
    mut v_x_3031_: *mut leanh::LeanObject,
    mut v_m_u2081_3032_: *mut leanh::LeanObject,
    mut v_m_u2082_3033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: u8 = 0;
    v_size_3034_ = leanh::lean_ctor_get(v_m_u2081_3032_, 0);
    v_buckets_3035_ = leanh::lean_ctor_get(v_m_u2081_3032_, 1);
    v_size_3036_ = leanh::lean_ctor_get(v_m_u2082_3033_, 0);
    v___x_3037_ = lean_nat_dec_le(v_size_3034_, v_size_3036_);
    if v___x_3037_ == 0 {
        let mut v___f_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___f_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3043_: usize = 0;
        let mut v___x_3044_: usize = 0;
        let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_3035_);
        leanh::lean_dec(v_m_u2081_3032_);
        v___f_3040_ = leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_3040_, 0, v_x_3030_);
        leanh::lean_closure_set(v___f_3040_, 1, v_x_3031_);
        v___x_3041_ = l_Std_ExtDHashMap_union___redArg___closed__9;
        v___f_3042_ = leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_3042_, 0, v___x_3041_);
        leanh::lean_closure_set(v___f_3042_, 1, v___f_3040_);
        v_sz_3043_ = lean_array_size(v_buckets_3035_);
        v___x_3044_ = 0usize;
        v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_3046_: *mut leanh::LeanObject,
    mut v_00_u03b2_3047_: *mut leanh::LeanObject,
    mut v_x_3048_: *mut leanh::LeanObject,
    mut v_x_3049_: *mut leanh::LeanObject,
    mut v_inst_3050_: *mut leanh::LeanObject,
    mut v_inst_3051_: *mut leanh::LeanObject,
    mut v_m_u2081_3052_: *mut leanh::LeanObject,
    mut v_m_u2082_3053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    v_size_3054_ = leanh::lean_ctor_get(v_m_u2081_3052_, 0);
    v_buckets_3055_ = leanh::lean_ctor_get(v_m_u2081_3052_, 1);
    v_size_3056_ = leanh::lean_ctor_get(v_m_u2082_3053_, 0);
    v___x_3057_ = lean_nat_dec_le(v_size_3054_, v_size_3056_);
    if v___x_3057_ == 0 {
        let mut v___f_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___f_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3063_: usize = 0;
        let mut v___x_3064_: usize = 0;
        let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_3055_);
        leanh::lean_dec(v_m_u2081_3052_);
        v___f_3060_ = leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_3060_, 0, v_x_3048_);
        leanh::lean_closure_set(v___f_3060_, 1, v_x_3049_);
        v___x_3061_ = l_Std_ExtDHashMap_union___redArg___closed__9;
        v___f_3062_ = leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_3062_, 0, v___x_3061_);
        leanh::lean_closure_set(v___f_3062_, 1, v___f_3060_);
        v_sz_3063_ = lean_array_size(v_buckets_3055_);
        v___x_3064_ = 0usize;
        v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_x_3066_: *mut leanh::LeanObject,
    mut v_x_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ =
        leanh::lean_alloc_closure(l_Std_ExtDHashMap_union as *mut core::ffi::c_void, 8, 6);
    leanh::lean_closure_set(v___x_3068_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3068_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3068_, 2, v_x_3066_);
    leanh::lean_closure_set(v___x_3068_, 3, v_x_3067_);
    leanh::lean_closure_set(v___x_3068_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3068_, 5, leanh::lean_box(0));
    return v___x_3068_;
}
pub unsafe fn l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3069_: *mut leanh::LeanObject,
    mut v_00_u03b2_3070_: *mut leanh::LeanObject,
    mut v_x_3071_: *mut leanh::LeanObject,
    mut v_x_3072_: *mut leanh::LeanObject,
    mut v_inst_3073_: *mut leanh::LeanObject,
    mut v_inst_3074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3075_ =
        leanh::lean_alloc_closure(l_Std_ExtDHashMap_union as *mut core::ffi::c_void, 8, 6);
    leanh::lean_closure_set(v___x_3075_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3075_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3075_, 2, v_x_3071_);
    leanh::lean_closure_set(v___x_3075_, 3, v_x_3072_);
    leanh::lean_closure_set(v___x_3075_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3075_, 5, leanh::lean_box(0));
    return v___x_3075_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(
    mut v_x_3076_: *mut leanh::LeanObject,
    mut v_x_3077_: *mut leanh::LeanObject,
    mut v_inst_3078_: *mut leanh::LeanObject,
    mut v_m_u2081_3079_: *mut leanh::LeanObject,
    mut v_m_u2082_3080_: *mut leanh::LeanObject,
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
    mut v_x_3082_: *mut leanh::LeanObject,
    mut v_x_3083_: *mut leanh::LeanObject,
    mut v_inst_3084_: *mut leanh::LeanObject,
    mut v_m_u2081_3085_: *mut leanh::LeanObject,
    mut v_m_u2082_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3087_: u8 = 0;
    let mut v_r_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(
        v_x_3082_,
        v_x_3083_,
        v_inst_3084_,
        v_m_u2081_3085_,
        v_m_u2082_3086_,
    );
    v_r_3088_ = leanh::lean_box((v_res_3087_) as usize);
    return v_r_3088_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg(
    mut v_x_3089_: *mut leanh::LeanObject,
    mut v_x_3090_: *mut leanh::LeanObject,
    mut v_inst_3091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3092_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_3092_, 0, v_x_3089_);
    leanh::lean_closure_set(v___f_3092_, 1, v_x_3090_);
    leanh::lean_closure_set(v___f_3092_, 2, v_inst_3091_);
    return v___f_3092_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq(
    mut v_00_u03b1_3093_: *mut leanh::LeanObject,
    mut v_00_u03b2_3094_: *mut leanh::LeanObject,
    mut v_x_3095_: *mut leanh::LeanObject,
    mut v_x_3096_: *mut leanh::LeanObject,
    mut v_inst_3097_: *mut leanh::LeanObject,
    mut v_inst_3098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3099_ = leanh::lean_alloc_closure(
        l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_3099_, 0, v_x_3095_);
    leanh::lean_closure_set(v___f_3099_, 1, v_x_3096_);
    leanh::lean_closure_set(v___f_3099_, 2, v_inst_3098_);
    return v___f_3099_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(
    mut v_inst_3100_: *mut leanh::LeanObject,
    mut v_inst_3101_: *mut leanh::LeanObject,
    mut v_inst_3102_: *mut leanh::LeanObject,
    mut v_x_3103_: *mut leanh::LeanObject,
    mut v_x_3104_: *mut leanh::LeanObject,
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
    mut v_inst_3106_: *mut leanh::LeanObject,
    mut v_inst_3107_: *mut leanh::LeanObject,
    mut v_inst_3108_: *mut leanh::LeanObject,
    mut v_x_3109_: *mut leanh::LeanObject,
    mut v_x_3110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3111_: u8 = 0;
    let mut v_r_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3111_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(
        v_inst_3106_,
        v_inst_3107_,
        v_inst_3108_,
        v_x_3109_,
        v_x_3110_,
    );
    v_r_3112_ = leanh::lean_box((v_res_3111_) as usize);
    return v_r_3112_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(
    mut v_00_u03b1_3113_: *mut leanh::LeanObject,
    mut v_00_u03b2_3114_: *mut leanh::LeanObject,
    mut v_inst_3115_: *mut leanh::LeanObject,
    mut v_inst_3116_: *mut leanh::LeanObject,
    mut v_inst_3117_: *mut leanh::LeanObject,
    mut v_inst_3118_: *mut leanh::LeanObject,
    mut v_inst_3119_: *mut leanh::LeanObject,
    mut v_x_3120_: *mut leanh::LeanObject,
    mut v_x_3121_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_3123_: *mut leanh::LeanObject,
    mut v_00_u03b2_3124_: *mut leanh::LeanObject,
    mut v_inst_3125_: *mut leanh::LeanObject,
    mut v_inst_3126_: *mut leanh::LeanObject,
    mut v_inst_3127_: *mut leanh::LeanObject,
    mut v_inst_3128_: *mut leanh::LeanObject,
    mut v_inst_3129_: *mut leanh::LeanObject,
    mut v_x_3130_: *mut leanh::LeanObject,
    mut v_x_3131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3132_: u8 = 0;
    let mut v_r_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    v_r_3133_ = leanh::lean_box((v_res_3132_) as usize);
    return v_r_3133_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_beq___redArg(
    mut v_x_3134_: *mut leanh::LeanObject,
    mut v_x_3135_: *mut leanh::LeanObject,
    mut v_inst_3136_: *mut leanh::LeanObject,
    mut v_m_u2081_3137_: *mut leanh::LeanObject,
    mut v_m_u2082_3138_: *mut leanh::LeanObject,
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
    mut v_x_3140_: *mut leanh::LeanObject,
    mut v_x_3141_: *mut leanh::LeanObject,
    mut v_inst_3142_: *mut leanh::LeanObject,
    mut v_m_u2081_3143_: *mut leanh::LeanObject,
    mut v_m_u2082_3144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3145_: u8 = 0;
    let mut v_r_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Std_ExtDHashMap_Const_beq___redArg(
        v_x_3140_,
        v_x_3141_,
        v_inst_3142_,
        v_m_u2081_3143_,
        v_m_u2082_3144_,
    );
    v_r_3146_ = leanh::lean_box((v_res_3145_) as usize);
    return v_r_3146_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_beq(
    mut v_00_u03b1_3147_: *mut leanh::LeanObject,
    mut v_x_3148_: *mut leanh::LeanObject,
    mut v_x_3149_: *mut leanh::LeanObject,
    mut v_00_u03b2_3150_: *mut leanh::LeanObject,
    mut v_inst_3151_: *mut leanh::LeanObject,
    mut v_inst_3152_: *mut leanh::LeanObject,
    mut v_inst_3153_: *mut leanh::LeanObject,
    mut v_m_u2081_3154_: *mut leanh::LeanObject,
    mut v_m_u2082_3155_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_3157_: *mut leanh::LeanObject,
    mut v_x_3158_: *mut leanh::LeanObject,
    mut v_x_3159_: *mut leanh::LeanObject,
    mut v_00_u03b2_3160_: *mut leanh::LeanObject,
    mut v_inst_3161_: *mut leanh::LeanObject,
    mut v_inst_3162_: *mut leanh::LeanObject,
    mut v_inst_3163_: *mut leanh::LeanObject,
    mut v_m_u2081_3164_: *mut leanh::LeanObject,
    mut v_m_u2082_3165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3166_: u8 = 0;
    let mut v_r_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    v_r_3167_ = leanh::lean_box((v_res_3166_) as usize);
    return v_r_3167_;
}
pub unsafe fn l_Std_ExtDHashMap_inter___redArg(
    mut v_x_3168_: *mut leanh::LeanObject,
    mut v_x_3169_: *mut leanh::LeanObject,
    mut v_m_u2081_3170_: *mut leanh::LeanObject,
    mut v_m_u2082_3171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3172_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_3168_,
        v_x_3169_,
        v_m_u2081_3170_,
        v_m_u2082_3171_,
    );
    return v___x_3172_;
}
pub unsafe fn l_Std_ExtDHashMap_inter(
    mut v_00_u03b1_3173_: *mut leanh::LeanObject,
    mut v_00_u03b2_3174_: *mut leanh::LeanObject,
    mut v_x_3175_: *mut leanh::LeanObject,
    mut v_x_3176_: *mut leanh::LeanObject,
    mut v_inst_3177_: *mut leanh::LeanObject,
    mut v_inst_3178_: *mut leanh::LeanObject,
    mut v_m_u2081_3179_: *mut leanh::LeanObject,
    mut v_m_u2082_3180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3181_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_3175_,
        v_x_3176_,
        v_m_u2081_3179_,
        v_m_u2082_3180_,
    );
    return v___x_3181_;
}
pub unsafe fn l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_3182_: *mut leanh::LeanObject,
    mut v_x_3183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3184_ =
        leanh::lean_alloc_closure(l_Std_ExtDHashMap_inter as *mut core::ffi::c_void, 8, 6);
    leanh::lean_closure_set(v___x_3184_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3184_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3184_, 2, v_x_3182_);
    leanh::lean_closure_set(v___x_3184_, 3, v_x_3183_);
    leanh::lean_closure_set(v___x_3184_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3184_, 5, leanh::lean_box(0));
    return v___x_3184_;
}
pub unsafe fn l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3185_: *mut leanh::LeanObject,
    mut v_00_u03b2_3186_: *mut leanh::LeanObject,
    mut v_x_3187_: *mut leanh::LeanObject,
    mut v_x_3188_: *mut leanh::LeanObject,
    mut v_inst_3189_: *mut leanh::LeanObject,
    mut v_inst_3190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ =
        leanh::lean_alloc_closure(l_Std_ExtDHashMap_inter as *mut core::ffi::c_void, 8, 6);
    leanh::lean_closure_set(v___x_3191_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3191_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3191_, 2, v_x_3187_);
    leanh::lean_closure_set(v___x_3191_, 3, v_x_3188_);
    leanh::lean_closure_set(v___x_3191_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3191_, 5, leanh::lean_box(0));
    return v___x_3191_;
}
pub unsafe fn l_Std_ExtDHashMap_diff___redArg___lam__0(
    mut v_x_3192_: *mut leanh::LeanObject,
    mut v_x_3193_: *mut leanh::LeanObject,
    mut v_m_u2082_3194_: *mut leanh::LeanObject,
    mut v___x_3195_: u8,
    mut v_k_3196_: *mut leanh::LeanObject,
    mut v_x_3197_: *mut leanh::LeanObject,
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
    mut v_x_3200_: *mut leanh::LeanObject,
    mut v_x_3201_: *mut leanh::LeanObject,
    mut v_m_u2082_3202_: *mut leanh::LeanObject,
    mut v___x_3203_: *mut leanh::LeanObject,
    mut v_k_3204_: *mut leanh::LeanObject,
    mut v_x_3205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_108__boxed_3206_: u8 = 0;
    let mut v_res_3207_: u8 = 0;
    let mut v_r_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_108__boxed_3206_ = (leanh::lean_unbox(v___x_3203_) as u8);
    v_res_3207_ = l_Std_ExtDHashMap_diff___redArg___lam__0(
        v_x_3200_,
        v_x_3201_,
        v_m_u2082_3202_,
        v___x_108__boxed_3206_,
        v_k_3204_,
        v_x_3205_,
    );
    leanh::lean_dec(v_x_3205_);
    leanh::lean_dec(v_m_u2082_3202_);
    v_r_3208_ = leanh::lean_box((v_res_3207_) as usize);
    return v_r_3208_;
}
pub unsafe fn l_Std_ExtDHashMap_diff___redArg(
    mut v_x_3209_: *mut leanh::LeanObject,
    mut v_x_3210_: *mut leanh::LeanObject,
    mut v_m_u2081_3211_: *mut leanh::LeanObject,
    mut v_m_u2082_3212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    v_size_3213_ = leanh::lean_ctor_get(v_m_u2081_3211_, 0);
    v_size_3214_ = leanh::lean_ctor_get(v_m_u2082_3212_, 0);
    v___x_3215_ = lean_nat_dec_le(v_size_3213_, v_size_3214_);
    if v___x_3215_ == 0 {
        let mut v___f_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3218_ = leanh::lean_box((v___x_3215_) as usize);
        v___f_3219_ = leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_3219_, 0, v_x_3209_);
        leanh::lean_closure_set(v___f_3219_, 1, v_x_3210_);
        leanh::lean_closure_set(v___f_3219_, 2, v_m_u2082_3212_);
        leanh::lean_closure_set(v___f_3219_, 3, v___x_3218_);
        v___x_3220_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3219_, v_m_u2081_3211_);
        return v___x_3220_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_diff(
    mut v_00_u03b1_3221_: *mut leanh::LeanObject,
    mut v_00_u03b2_3222_: *mut leanh::LeanObject,
    mut v_x_3223_: *mut leanh::LeanObject,
    mut v_x_3224_: *mut leanh::LeanObject,
    mut v_inst_3225_: *mut leanh::LeanObject,
    mut v_inst_3226_: *mut leanh::LeanObject,
    mut v_m_u2081_3227_: *mut leanh::LeanObject,
    mut v_m_u2082_3228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    v_size_3229_ = leanh::lean_ctor_get(v_m_u2081_3227_, 0);
    v_size_3230_ = leanh::lean_ctor_get(v_m_u2082_3228_, 0);
    v___x_3231_ = lean_nat_dec_le(v_size_3229_, v_size_3230_);
    if v___x_3231_ == 0 {
        let mut v___f_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3234_ = leanh::lean_box((v___x_3231_) as usize);
        v___f_3235_ = leanh::lean_alloc_closure(
            l_Std_ExtDHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_3235_, 0, v_x_3223_);
        leanh::lean_closure_set(v___f_3235_, 1, v_x_3224_);
        leanh::lean_closure_set(v___f_3235_, 2, v_m_u2082_3228_);
        leanh::lean_closure_set(v___f_3235_, 3, v___x_3234_);
        v___x_3236_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3235_, v_m_u2081_3227_);
        return v___x_3236_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_3237_: *mut leanh::LeanObject,
    mut v_x_3238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3239_ =
        leanh::lean_alloc_closure(l_Std_ExtDHashMap_diff as *mut core::ffi::c_void, 8, 6);
    leanh::lean_closure_set(v___x_3239_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3239_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3239_, 2, v_x_3237_);
    leanh::lean_closure_set(v___x_3239_, 3, v_x_3238_);
    leanh::lean_closure_set(v___x_3239_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3239_, 5, leanh::lean_box(0));
    return v___x_3239_;
}
pub unsafe fn l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3240_: *mut leanh::LeanObject,
    mut v_00_u03b2_3241_: *mut leanh::LeanObject,
    mut v_x_3242_: *mut leanh::LeanObject,
    mut v_x_3243_: *mut leanh::LeanObject,
    mut v_inst_3244_: *mut leanh::LeanObject,
    mut v_inst_3245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ =
        leanh::lean_alloc_closure(l_Std_ExtDHashMap_diff as *mut core::ffi::c_void, 8, 6);
    leanh::lean_closure_set(v___x_3246_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3246_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3246_, 2, v_x_3242_);
    leanh::lean_closure_set(v___x_3246_, 3, v_x_3243_);
    leanh::lean_closure_set(v___x_3246_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3246_, 5, leanh::lean_box(0));
    return v___x_3246_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_unitOfArray___redArg(
    mut v_inst_3251_: *mut leanh::LeanObject,
    mut v_inst_3252_: *mut leanh::LeanObject,
    mut v_l_3253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3254_ = l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_3255_ = leanh::lean_obj_once(
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
    mut v_00_u03b1_3257_: *mut leanh::LeanObject,
    mut v_inst_3258_: *mut leanh::LeanObject,
    mut v_inst_3259_: *mut leanh::LeanObject,
    mut v_l_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3261_ = l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_3262_ = leanh::lean_obj_once(
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
    mut v_inst_3268_: *mut leanh::LeanObject,
    mut v_inst_3269_: *mut leanh::LeanObject,
    mut v_l_3270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3271_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3272_ = leanh::lean_obj_once(
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
    mut v_00_u03b1_3274_: *mut leanh::LeanObject,
    mut v_00_u03b2_3275_: *mut leanh::LeanObject,
    mut v_inst_3276_: *mut leanh::LeanObject,
    mut v_inst_3277_: *mut leanh::LeanObject,
    mut v_l_3278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3279_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3280_ = leanh::lean_obj_once(
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
    mut v_inst_3282_: *mut leanh::LeanObject,
    mut v_inst_3283_: *mut leanh::LeanObject,
    mut v_l_3284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3285_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3286_ = leanh::lean_obj_once(
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
    mut v_00_u03b1_3288_: *mut leanh::LeanObject,
    mut v_00_u03b2_3289_: *mut leanh::LeanObject,
    mut v_inst_3290_: *mut leanh::LeanObject,
    mut v_inst_3291_: *mut leanh::LeanObject,
    mut v_l_3292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3293_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3294_ = leanh::lean_obj_once(
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
    mut v_inst_3296_: *mut leanh::LeanObject,
    mut v_inst_3297_: *mut leanh::LeanObject,
    mut v_l_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3299_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3300_ = leanh::lean_obj_once(
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
    mut v_00_u03b1_3302_: *mut leanh::LeanObject,
    mut v_inst_3303_: *mut leanh::LeanObject,
    mut v_inst_3304_: *mut leanh::LeanObject,
    mut v_l_3305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3306_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3307_ = leanh::lean_obj_once(
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtDHashMap_Basic(
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
pub unsafe fn initialize_Std_Data_ExtDHashMap_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtDHashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtDHashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_ExtDHashMap_Basic(builtin);
}