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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_uint64, lean_unsigned_to_nat,
};
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtDHashMap_instEmptyCollection___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDHashMap_union___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_ExtDHashMap_union___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_ExtDHashMap_union___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_ExtDHashMap_union___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_union___redArg___closed__10_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_union___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__10_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_ExtDHashMap_ofList___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_union___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_ofList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_ExtDHashMap_ofList___redArg___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_ExtDHashMap_ofList___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtDHashMap_ofList___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Std_ExtDHashMap_mk___redArg(mut v_m_1655_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_m_1655_);
    return v_m_1655_;
}
pub unsafe fn l_Std_ExtDHashMap_mk___redArg___boxed(
    mut v_m_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1657_: *mut LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Std_ExtDHashMap_mk___redArg(v_m_1656_);
    lean_dec_ref(v_m_1656_);
    return v_res_1657_;
}
pub unsafe fn l_Std_ExtDHashMap_mk(
    mut v_00_u03b1_1658_: *mut LeanObject,
    mut v_00_u03b2_1659_: *mut LeanObject,
    mut v_x_1660_: *mut LeanObject,
    mut v_x_1661_: *mut LeanObject,
    mut v_m_1662_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_m_1662_);
    return v_m_1662_;
}
pub unsafe fn l_Std_ExtDHashMap_mk___boxed(
    mut v_00_u03b1_1663_: *mut LeanObject,
    mut v_00_u03b2_1664_: *mut LeanObject,
    mut v_x_1665_: *mut LeanObject,
    mut v_x_1666_: *mut LeanObject,
    mut v_m_1667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1668_: *mut LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_ExtDHashMap_mk(
        v_00_u03b1_1663_,
        v_00_u03b2_1664_,
        v_x_1665_,
        v_x_1666_,
        v_m_1667_,
    );
    lean_dec_ref(v_m_1667_);
    lean_dec_ref(v_x_1666_);
    lean_dec_ref(v_x_1665_);
    return v_res_1668_;
}
pub unsafe fn l_Std_ExtDHashMap_lift___redArg(
    mut v_f_1669_: *mut LeanObject,
    mut v_m_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = lean_apply_1(v_f_1669_, v_m_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Std_ExtDHashMap_lift(
    mut v_00_u03b1_1672_: *mut LeanObject,
    mut v_00_u03b2_1673_: *mut LeanObject,
    mut v_x_1674_: *mut LeanObject,
    mut v_x_1675_: *mut LeanObject,
    mut v_00_u03b3_1676_: *mut LeanObject,
    mut v_f_1677_: *mut LeanObject,
    mut v_h_1678_: *mut LeanObject,
    mut v_m_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    v___x_1680_ = lean_apply_1(v_f_1677_, v_m_1679_);
    return v___x_1680_;
}
pub unsafe fn l_Std_ExtDHashMap_lift___boxed(
    mut v_00_u03b1_1681_: *mut LeanObject,
    mut v_00_u03b2_1682_: *mut LeanObject,
    mut v_x_1683_: *mut LeanObject,
    mut v_x_1684_: *mut LeanObject,
    mut v_00_u03b3_1685_: *mut LeanObject,
    mut v_f_1686_: *mut LeanObject,
    mut v_h_1687_: *mut LeanObject,
    mut v_m_1688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1689_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_x_1684_);
    lean_dec_ref(v_x_1683_);
    return v_res_1689_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082___redArg(
    mut v_f_1690_: *mut LeanObject,
    mut v_m_u2081_1691_: *mut LeanObject,
    mut v_m_u2082_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    v___x_1693_ = lean_apply_2(v_f_1690_, v_m_u2081_1691_, v_m_u2082_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082(
    mut v_00_u03b1_1694_: *mut LeanObject,
    mut v_00_u03b2_1695_: *mut LeanObject,
    mut v_x_1696_: *mut LeanObject,
    mut v_x_1697_: *mut LeanObject,
    mut v_00_u03b3_1698_: *mut LeanObject,
    mut v_f_1699_: *mut LeanObject,
    mut v_h_1700_: *mut LeanObject,
    mut v_m_u2081_1701_: *mut LeanObject,
    mut v_m_u2082_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    v___x_1703_ = lean_apply_2(v_f_1699_, v_m_u2081_1701_, v_m_u2082_1702_);
    return v___x_1703_;
}
pub unsafe fn l_Std_ExtDHashMap_lift_u2082___boxed(
    mut v_00_u03b1_1704_: *mut LeanObject,
    mut v_00_u03b2_1705_: *mut LeanObject,
    mut v_x_1706_: *mut LeanObject,
    mut v_x_1707_: *mut LeanObject,
    mut v_00_u03b3_1708_: *mut LeanObject,
    mut v_f_1709_: *mut LeanObject,
    mut v_h_1710_: *mut LeanObject,
    mut v_m_u2081_1711_: *mut LeanObject,
    mut v_m_u2082_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1713_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_x_1707_);
    lean_dec_ref(v_x_1706_);
    return v_res_1713_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn___redArg(
    mut v_m_1714_: *mut LeanObject,
    mut v_f_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_apply_2(v_f_1715_, v_m_1714_, lean_box(0));
    return v___x_1716_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn(
    mut v_00_u03b1_1717_: *mut LeanObject,
    mut v_00_u03b2_1718_: *mut LeanObject,
    mut v_x_1719_: *mut LeanObject,
    mut v_x_1720_: *mut LeanObject,
    mut v_00_u03b3_1721_: *mut LeanObject,
    mut v_m_1722_: *mut LeanObject,
    mut v_f_1723_: *mut LeanObject,
    mut v_h_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_1725_ = lean_apply_2(v_f_1723_, v_m_1722_, lean_box(0));
    return v___x_1725_;
}
pub unsafe fn l_Std_ExtDHashMap_pliftOn___boxed(
    mut v_00_u03b1_1726_: *mut LeanObject,
    mut v_00_u03b2_1727_: *mut LeanObject,
    mut v_x_1728_: *mut LeanObject,
    mut v_x_1729_: *mut LeanObject,
    mut v_00_u03b3_1730_: *mut LeanObject,
    mut v_m_1731_: *mut LeanObject,
    mut v_f_1732_: *mut LeanObject,
    mut v_h_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1734_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_x_1729_);
    lean_dec_ref(v_x_1728_);
    return v_res_1734_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___redArg(
    mut v_capacity_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    v___x_1736_ = lean_unsigned_to_nat(0);
    v___x_1737_ = lean_unsigned_to_nat(4);
    v___x_1738_ = lean_nat_mul(v_capacity_1735_, v___x_1737_);
    v___x_1739_ = lean_unsigned_to_nat(3);
    v___x_1740_ = lean_nat_div(v___x_1738_, v___x_1739_);
    lean_dec(v___x_1738_);
    v___x_1741_ = l_Nat_nextPowerOfTwo(v___x_1740_);
    lean_dec(v___x_1740_);
    v___x_1742_ = lean_box(0);
    v___x_1743_ = lean_mk_array(v___x_1741_, v___x_1742_);
    v___x_1744_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1744_, 0, v___x_1736_);
    lean_ctor_set(v___x_1744_, 1, v___x_1743_);
    return v___x_1744_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___redArg___boxed(
    mut v_capacity_1745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1746_: *mut LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Std_ExtDHashMap_emptyWithCapacity___redArg(v_capacity_1745_);
    lean_dec(v_capacity_1745_);
    return v_res_1746_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity(
    mut v_00_u03b1_1747_: *mut LeanObject,
    mut v_00_u03b2_1748_: *mut LeanObject,
    mut v_inst_1749_: *mut LeanObject,
    mut v_inst_1750_: *mut LeanObject,
    mut v_capacity_1751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    v___x_1752_ = lean_unsigned_to_nat(0);
    v___x_1753_ = lean_unsigned_to_nat(4);
    v___x_1754_ = lean_nat_mul(v_capacity_1751_, v___x_1753_);
    v___x_1755_ = lean_unsigned_to_nat(3);
    v___x_1756_ = lean_nat_div(v___x_1754_, v___x_1755_);
    lean_dec(v___x_1754_);
    v___x_1757_ = l_Nat_nextPowerOfTwo(v___x_1756_);
    lean_dec(v___x_1756_);
    v___x_1758_ = lean_box(0);
    v___x_1759_ = lean_mk_array(v___x_1757_, v___x_1758_);
    v___x_1760_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1760_, 0, v___x_1752_);
    lean_ctor_set(v___x_1760_, 1, v___x_1759_);
    return v___x_1760_;
}
pub unsafe fn l_Std_ExtDHashMap_emptyWithCapacity___boxed(
    mut v_00_u03b1_1761_: *mut LeanObject,
    mut v_00_u03b2_1762_: *mut LeanObject,
    mut v_inst_1763_: *mut LeanObject,
    mut v_inst_1764_: *mut LeanObject,
    mut v_capacity_1765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1766_: *mut LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Std_ExtDHashMap_emptyWithCapacity(
        v_00_u03b1_1761_,
        v_00_u03b2_1762_,
        v_inst_1763_,
        v_inst_1764_,
        v_capacity_1765_,
    );
    lean_dec(v_capacity_1765_);
    lean_dec_ref(v_inst_1764_);
    lean_dec_ref(v_inst_1763_);
    return v_res_1766_;
}
pub unsafe fn _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0() -> *mut LeanObject {
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    v___x_1767_ = lean_box(0);
    v___x_1768_ = lean_unsigned_to_nat(16);
    v___x_1769_ = lean_mk_array(v___x_1768_, v___x_1767_);
    return v___x_1769_;
}
pub unsafe fn _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1() -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    v___x_1770_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__0_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0,
    );
    v___x_1771_ = lean_unsigned_to_nat(0);
    v___x_1772_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    lean_ctor_set(v___x_1772_, 1, v___x_1770_);
    return v___x_1772_;
}
pub unsafe fn l_Std_ExtDHashMap_instEmptyCollection(
    mut v_00_u03b1_1773_: *mut LeanObject,
    mut v_00_u03b2_1774_: *mut LeanObject,
    mut v_inst_1775_: *mut LeanObject,
    mut v_inst_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    v___x_1777_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    return v___x_1777_;
}
pub unsafe fn l_Std_ExtDHashMap_instEmptyCollection___boxed(
    mut v_00_u03b1_1778_: *mut LeanObject,
    mut v_00_u03b2_1779_: *mut LeanObject,
    mut v_inst_1780_: *mut LeanObject,
    mut v_inst_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1782_: *mut LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Std_ExtDHashMap_instEmptyCollection(
        v_00_u03b1_1778_,
        v_00_u03b2_1779_,
        v_inst_1780_,
        v_inst_1781_,
    );
    lean_dec_ref(v_inst_1781_);
    lean_dec_ref(v_inst_1780_);
    return v_res_1782_;
}
pub unsafe fn l_Std_ExtDHashMap_instInhabited(
    mut v_00_u03b1_1783_: *mut LeanObject,
    mut v_00_u03b2_1784_: *mut LeanObject,
    mut v_inst_1785_: *mut LeanObject,
    mut v_inst_1786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    v___x_1787_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtDHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1,
    );
    return v___x_1787_;
}
pub unsafe fn l_Std_ExtDHashMap_instInhabited___boxed(
    mut v_00_u03b1_1788_: *mut LeanObject,
    mut v_00_u03b2_1789_: *mut LeanObject,
    mut v_inst_1790_: *mut LeanObject,
    mut v_inst_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1792_: *mut LeanObject = core::ptr::null_mut();
    v_res_1792_ = l_Std_ExtDHashMap_instInhabited(
        v_00_u03b1_1788_,
        v_00_u03b2_1789_,
        v_inst_1790_,
        v_inst_1791_,
    );
    lean_dec_ref(v_inst_1791_);
    lean_dec_ref(v_inst_1790_);
    return v_res_1792_;
}
pub unsafe fn l_Std_ExtDHashMap_insert___redArg(
    mut v_x_1793_: *mut LeanObject,
    mut v_x_1794_: *mut LeanObject,
    mut v_m_1795_: *mut LeanObject,
    mut v_a_1796_: *mut LeanObject,
    mut v_b_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1793_, v_x_1794_, v_m_1795_, v_a_1796_, v_b_1797_,
    );
    return v___x_1798_;
}
pub unsafe fn l_Std_ExtDHashMap_insert(
    mut v_00_u03b1_1799_: *mut LeanObject,
    mut v_00_u03b2_1800_: *mut LeanObject,
    mut v_x_1801_: *mut LeanObject,
    mut v_x_1802_: *mut LeanObject,
    mut v_inst_1803_: *mut LeanObject,
    mut v_inst_1804_: *mut LeanObject,
    mut v_m_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
    mut v_b_1807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    v___x_1808_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_1801_, v_x_1802_, v_m_1805_, v_a_1806_, v_b_1807_,
    );
    return v___x_1808_;
}
pub unsafe fn l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1809_: *mut LeanObject,
    mut v_x_1810_: *mut LeanObject,
    mut v_x_1811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1812_ = lean_ctor_get(v_x_1811_, 0);
    lean_inc(v_fst_1812_);
    v_snd_1813_ = lean_ctor_get(v_x_1811_, 1);
    lean_inc(v_snd_1813_);
    lean_dec_ref(v_x_1811_);
    v___x_1814_ = lean_obj_once(
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
    mut v_x_1816_: *mut LeanObject,
    mut v_x_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1818_: *mut LeanObject = core::ptr::null_mut();
    v___f_1818_ = lean_alloc_closure(
        l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1818_, 0, v_x_1816_);
    lean_closure_set(v___f_1818_, 1, v_x_1817_);
    return v___f_1818_;
}
pub unsafe fn l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1819_: *mut LeanObject,
    mut v_00_u03b2_1820_: *mut LeanObject,
    mut v_x_1821_: *mut LeanObject,
    mut v_x_1822_: *mut LeanObject,
    mut v_inst_1823_: *mut LeanObject,
    mut v_inst_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1825_: *mut LeanObject = core::ptr::null_mut();
    v___f_1825_ = lean_alloc_closure(
        l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1825_, 0, v_x_1821_);
    lean_closure_set(v___f_1825_, 1, v_x_1822_);
    return v___f_1825_;
}
pub unsafe fn l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1826_: *mut LeanObject,
    mut v_x_1827_: *mut LeanObject,
    mut v_x_1828_: *mut LeanObject,
    mut v_x_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1830_ = lean_ctor_get(v_x_1828_, 0);
    lean_inc(v_fst_1830_);
    v_snd_1831_ = lean_ctor_get(v_x_1828_, 1);
    lean_inc(v_snd_1831_);
    lean_dec_ref(v_x_1828_);
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
    mut v_x_1833_: *mut LeanObject,
    mut v_x_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1835_: *mut LeanObject = core::ptr::null_mut();
    v___f_1835_ = lean_alloc_closure(
        l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1835_, 0, v_x_1833_);
    lean_closure_set(v___f_1835_, 1, v_x_1834_);
    return v___f_1835_;
}
pub unsafe fn l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1836_: *mut LeanObject,
    mut v_00_u03b2_1837_: *mut LeanObject,
    mut v_x_1838_: *mut LeanObject,
    mut v_x_1839_: *mut LeanObject,
    mut v_inst_1840_: *mut LeanObject,
    mut v_inst_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1842_: *mut LeanObject = core::ptr::null_mut();
    v___f_1842_ = lean_alloc_closure(
        l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1842_, 0, v_x_1838_);
    lean_closure_set(v___f_1842_, 1, v_x_1839_);
    return v___f_1842_;
}
pub unsafe fn l_Std_ExtDHashMap_insertIfNew___redArg(
    mut v_x_1843_: *mut LeanObject,
    mut v_x_1844_: *mut LeanObject,
    mut v_m_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
    mut v_b_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1843_, v_x_1844_, v_m_1845_, v_a_1846_, v_b_1847_,
    );
    return v___x_1848_;
}
pub unsafe fn l_Std_ExtDHashMap_insertIfNew(
    mut v_00_u03b1_1849_: *mut LeanObject,
    mut v_00_u03b2_1850_: *mut LeanObject,
    mut v_x_1851_: *mut LeanObject,
    mut v_x_1852_: *mut LeanObject,
    mut v_inst_1853_: *mut LeanObject,
    mut v_inst_1854_: *mut LeanObject,
    mut v_m_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_b_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1851_, v_x_1852_, v_m_1855_, v_a_1856_, v_b_1857_,
    );
    return v___x_1858_;
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsert___redArg(
    mut v_x_1859_: *mut LeanObject,
    mut v_x_1860_: *mut LeanObject,
    mut v_m_1861_: *mut LeanObject,
    mut v_a_1862_: *mut LeanObject,
    mut v_b_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1868_: u8 = 0;
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v_val_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1864_ = lean_ctor_get(v_m_1861_, 0);
                v_buckets_1865_ = lean_ctor_get(v_m_1861_, 1);
                v_isSharedCheck_1916_ = (!lean_is_exclusive(v_m_1861_)) as u8;
                if v_isSharedCheck_1916_ == 0 {
                    v___x_1867_ = v_m_1861_;
                    v_isShared_1868_ = v_isSharedCheck_1916_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1865_);
                    lean_inc(v_size_1864_);
                    lean_dec(v_m_1861_);
                    v___x_1867_ = lean_box(0);
                    v_isShared_1868_ = v_isSharedCheck_1916_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1869_ = lean_array_get_size(v_buckets_1865_);
                lean_inc_ref(v_x_1860_);
                lean_inc_n(v_a_1862_, 2);
                v___x_1870_ = lean_apply_1(v_x_1860_, v_a_1862_);
                v___x_1871_ = 32u64;
                v___x_1872_ = lean_unbox_uint64(v___x_1870_);
                v___x_1873_ = lean_uint64_shift_right(v___x_1872_, v___x_1871_);
                v___x_1874_ = lean_unbox_uint64(v___x_1870_);
                lean_dec_ref(v___x_1870_);
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
                lean_inc(v_bkt_1884_);
                lean_inc_ref(v_x_1859_);
                v___x_1885_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1859_,
                    v_a_1862_,
                    v_bkt_1884_,
                );
                if v___x_1885_ == 0 {
                    lean_dec_ref(v_x_1859_);
                    v___x_1886_ = lean_unsigned_to_nat(1);
                    v_size_x27_1887_ = lean_nat_add(v_size_1864_, v___x_1886_);
                    lean_dec(v_size_1864_);
                    lean_inc(v_bkt_1884_);
                    v___x_1888_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1888_, 0, v_a_1862_);
                    lean_ctor_set(v___x_1888_, 1, v_b_1863_);
                    lean_ctor_set(v___x_1888_, 2, v_bkt_1884_);
                    v_buckets_x27_1889_ =
                        lean_array_uset(v_buckets_1865_, v___x_1883_, v___x_1888_);
                    v___x_1890_ = lean_unsigned_to_nat(4);
                    v___x_1891_ = lean_nat_mul(v_size_x27_1887_, v___x_1890_);
                    v___x_1892_ = lean_unsigned_to_nat(3);
                    v___x_1893_ = lean_nat_div(v___x_1891_, v___x_1892_);
                    lean_dec(v___x_1891_);
                    v___x_1894_ = lean_array_get_size(v_buckets_x27_1889_);
                    v___x_1895_ = lean_nat_dec_le(v___x_1893_, v___x_1894_);
                    lean_dec(v___x_1893_);
                    if v___x_1895_ == 0 {
                        v_val_1896_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_1860_,
                            v_buckets_x27_1889_,
                        );
                        if v_isShared_1868_ == 0 {
                            lean_ctor_set(v___x_1867_, 1, v_val_1896_);
                            lean_ctor_set(v___x_1867_, 0, v_size_x27_1887_);
                            v___x_1898_ = v___x_1867_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_size_x27_1887_);
                            lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_val_1896_);
                            v___x_1898_ = v_reuseFailAlloc_1901_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_x_1860_);
                        if v_isShared_1868_ == 0 {
                            lean_ctor_set(v___x_1867_, 1, v_buckets_x27_1889_);
                            lean_ctor_set(v___x_1867_, 0, v_size_x27_1887_);
                            v___x_1903_ = v___x_1867_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_size_x27_1887_);
                            lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_buckets_x27_1889_);
                            v___x_1903_ = v_reuseFailAlloc_1906_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1884_);
                    lean_dec_ref(v_x_1860_);
                    v___x_1907_ = lean_box(0);
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
                        lean_ctor_set(v___x_1867_, 1, v___x_1910_);
                        v___x_1912_ = v___x_1867_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_size_1864_);
                        lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1910_);
                        v___x_1912_ = v_reuseFailAlloc_1915_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1899_ = lean_box((v___x_1885_) as usize);
                v___x_1900_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1900_, 0, v___x_1899_);
                lean_ctor_set(v___x_1900_, 1, v___x_1898_);
                return v___x_1900_;
            }
            3 => {
                v___x_1904_ = lean_box((v___x_1885_) as usize);
                v___x_1905_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                lean_ctor_set(v___x_1905_, 1, v___x_1903_);
                return v___x_1905_;
            }
            4 => {
                v___x_1913_ = lean_box((v___x_1885_) as usize);
                v___x_1914_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1914_, 0, v___x_1913_);
                lean_ctor_set(v___x_1914_, 1, v___x_1912_);
                return v___x_1914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsert(
    mut v_00_u03b1_1917_: *mut LeanObject,
    mut v_00_u03b2_1918_: *mut LeanObject,
    mut v_x_1919_: *mut LeanObject,
    mut v_x_1920_: *mut LeanObject,
    mut v_inst_1921_: *mut LeanObject,
    mut v_inst_1922_: *mut LeanObject,
    mut v_m_1923_: *mut LeanObject,
    mut v_a_1924_: *mut LeanObject,
    mut v_b_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: u8 = 0;
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v_val_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1926_ = lean_ctor_get(v_m_1923_, 0);
                v_buckets_1927_ = lean_ctor_get(v_m_1923_, 1);
                v_isSharedCheck_1978_ = (!lean_is_exclusive(v_m_1923_)) as u8;
                if v_isSharedCheck_1978_ == 0 {
                    v___x_1929_ = v_m_1923_;
                    v_isShared_1930_ = v_isSharedCheck_1978_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1927_);
                    lean_inc(v_size_1926_);
                    lean_dec(v_m_1923_);
                    v___x_1929_ = lean_box(0);
                    v_isShared_1930_ = v_isSharedCheck_1978_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1931_ = lean_array_get_size(v_buckets_1927_);
                lean_inc_ref(v_x_1920_);
                lean_inc_n(v_a_1924_, 2);
                v___x_1932_ = lean_apply_1(v_x_1920_, v_a_1924_);
                v___x_1933_ = 32u64;
                v___x_1934_ = lean_unbox_uint64(v___x_1932_);
                v___x_1935_ = lean_uint64_shift_right(v___x_1934_, v___x_1933_);
                v___x_1936_ = lean_unbox_uint64(v___x_1932_);
                lean_dec_ref(v___x_1932_);
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
                lean_inc(v_bkt_1946_);
                lean_inc_ref(v_x_1919_);
                v___x_1947_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1919_,
                    v_a_1924_,
                    v_bkt_1946_,
                );
                if v___x_1947_ == 0 {
                    lean_dec_ref(v_x_1919_);
                    v___x_1948_ = lean_unsigned_to_nat(1);
                    v_size_x27_1949_ = lean_nat_add(v_size_1926_, v___x_1948_);
                    lean_dec(v_size_1926_);
                    lean_inc(v_bkt_1946_);
                    v___x_1950_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1950_, 0, v_a_1924_);
                    lean_ctor_set(v___x_1950_, 1, v_b_1925_);
                    lean_ctor_set(v___x_1950_, 2, v_bkt_1946_);
                    v_buckets_x27_1951_ =
                        lean_array_uset(v_buckets_1927_, v___x_1945_, v___x_1950_);
                    v___x_1952_ = lean_unsigned_to_nat(4);
                    v___x_1953_ = lean_nat_mul(v_size_x27_1949_, v___x_1952_);
                    v___x_1954_ = lean_unsigned_to_nat(3);
                    v___x_1955_ = lean_nat_div(v___x_1953_, v___x_1954_);
                    lean_dec(v___x_1953_);
                    v___x_1956_ = lean_array_get_size(v_buckets_x27_1951_);
                    v___x_1957_ = lean_nat_dec_le(v___x_1955_, v___x_1956_);
                    lean_dec(v___x_1955_);
                    if v___x_1957_ == 0 {
                        v_val_1958_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_1920_,
                            v_buckets_x27_1951_,
                        );
                        if v_isShared_1930_ == 0 {
                            lean_ctor_set(v___x_1929_, 1, v_val_1958_);
                            lean_ctor_set(v___x_1929_, 0, v_size_x27_1949_);
                            v___x_1960_ = v___x_1929_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_size_x27_1949_);
                            lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_val_1958_);
                            v___x_1960_ = v_reuseFailAlloc_1963_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_x_1920_);
                        if v_isShared_1930_ == 0 {
                            lean_ctor_set(v___x_1929_, 1, v_buckets_x27_1951_);
                            lean_ctor_set(v___x_1929_, 0, v_size_x27_1949_);
                            v___x_1965_ = v___x_1929_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_size_x27_1949_);
                            lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_buckets_x27_1951_);
                            v___x_1965_ = v_reuseFailAlloc_1968_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1946_);
                    lean_dec_ref(v_x_1920_);
                    v___x_1969_ = lean_box(0);
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
                        lean_ctor_set(v___x_1929_, 1, v___x_1972_);
                        v___x_1974_ = v___x_1929_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_size_1926_);
                        lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1972_);
                        v___x_1974_ = v_reuseFailAlloc_1977_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1961_ = lean_box((v___x_1947_) as usize);
                v___x_1962_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1962_, 0, v___x_1961_);
                lean_ctor_set(v___x_1962_, 1, v___x_1960_);
                return v___x_1962_;
            }
            3 => {
                v___x_1966_ = lean_box((v___x_1947_) as usize);
                v___x_1967_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1967_, 0, v___x_1966_);
                lean_ctor_set(v___x_1967_, 1, v___x_1965_);
                return v___x_1967_;
            }
            4 => {
                v___x_1975_ = lean_box((v___x_1947_) as usize);
                v___x_1976_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1976_, 0, v___x_1975_);
                lean_ctor_set(v___x_1976_, 1, v___x_1974_);
                return v___x_1976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsertIfNew___redArg(
    mut v_x_1979_: *mut LeanObject,
    mut v_x_1980_: *mut LeanObject,
    mut v_m_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
    mut v_b_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: u8 = 0;
    let mut v_val_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2027_: u8 = 0;
    let mut v_unused_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1984_ = lean_ctor_get(v_m_1981_, 0);
                v_buckets_1985_ = lean_ctor_get(v_m_1981_, 1);
                v___x_1986_ = lean_array_get_size(v_buckets_1985_);
                lean_inc_ref(v_x_1980_);
                lean_inc_n(v_a_1982_, 2);
                v___x_1987_ = lean_apply_1(v_x_1980_, v_a_1982_);
                v___x_1988_ = 32u64;
                v___x_1989_ = lean_unbox_uint64(v___x_1987_);
                v___x_1990_ = lean_uint64_shift_right(v___x_1989_, v___x_1988_);
                v___x_1991_ = lean_unbox_uint64(v___x_1987_);
                lean_dec_ref(v___x_1987_);
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
                lean_inc(v_bkt_2001_);
                v___x_2002_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1979_,
                    v_a_1982_,
                    v_bkt_2001_,
                );
                if v___x_2002_ == 0 {
                    lean_inc_ref(v_buckets_1985_);
                    lean_inc(v_size_1984_);
                    v_isSharedCheck_2027_ = (!lean_is_exclusive(v_m_1981_)) as u8;
                    if v_isSharedCheck_2027_ == 0 {
                        v_unused_2028_ = lean_ctor_get(v_m_1981_, 1);
                        lean_dec(v_unused_2028_);
                        v_unused_2029_ = lean_ctor_get(v_m_1981_, 0);
                        lean_dec(v_unused_2029_);
                        v___x_2004_ = v_m_1981_;
                        v_isShared_2005_ = v_isSharedCheck_2027_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_1981_);
                        v___x_2004_ = lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2027_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1983_);
                    lean_dec(v_a_1982_);
                    lean_dec_ref(v_x_1980_);
                    v___x_2030_ = lean_box((v___x_2002_) as usize);
                    v___x_2031_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2031_, 0, v___x_2030_);
                    lean_ctor_set(v___x_2031_, 1, v_m_1981_);
                    return v___x_2031_;
                }
            }
            1 => {
                v___x_2006_ = lean_unsigned_to_nat(1);
                v_size_x27_2007_ = lean_nat_add(v_size_1984_, v___x_2006_);
                lean_dec(v_size_1984_);
                lean_inc(v_bkt_2001_);
                v___x_2008_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2008_, 0, v_a_1982_);
                lean_ctor_set(v___x_2008_, 1, v_b_1983_);
                lean_ctor_set(v___x_2008_, 2, v_bkt_2001_);
                v_buckets_x27_2009_ = lean_array_uset(v_buckets_1985_, v___x_2000_, v___x_2008_);
                v___x_2010_ = lean_unsigned_to_nat(4);
                v___x_2011_ = lean_nat_mul(v_size_x27_2007_, v___x_2010_);
                v___x_2012_ = lean_unsigned_to_nat(3);
                v___x_2013_ = lean_nat_div(v___x_2011_, v___x_2012_);
                lean_dec(v___x_2011_);
                v___x_2014_ = lean_array_get_size(v_buckets_x27_2009_);
                v___x_2015_ = lean_nat_dec_le(v___x_2013_, v___x_2014_);
                lean_dec(v___x_2013_);
                if v___x_2015_ == 0 {
                    v_val_2016_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1980_,
                        v_buckets_x27_2009_,
                    );
                    if v_isShared_2005_ == 0 {
                        lean_ctor_set(v___x_2004_, 1, v_val_2016_);
                        lean_ctor_set(v___x_2004_, 0, v_size_x27_2007_);
                        v___x_2018_ = v___x_2004_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_size_x27_2007_);
                        lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_val_2016_);
                        v___x_2018_ = v_reuseFailAlloc_2021_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_1980_);
                    if v_isShared_2005_ == 0 {
                        lean_ctor_set(v___x_2004_, 1, v_buckets_x27_2009_);
                        lean_ctor_set(v___x_2004_, 0, v_size_x27_2007_);
                        v___x_2023_ = v___x_2004_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_size_x27_2007_);
                        lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_buckets_x27_2009_);
                        v___x_2023_ = v_reuseFailAlloc_2026_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2019_ = lean_box((v___x_2002_) as usize);
                v___x_2020_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2020_, 0, v___x_2019_);
                lean_ctor_set(v___x_2020_, 1, v___x_2018_);
                return v___x_2020_;
            }
            3 => {
                v___x_2024_ = lean_box((v___x_2002_) as usize);
                v___x_2025_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2025_, 0, v___x_2024_);
                lean_ctor_set(v___x_2025_, 1, v___x_2023_);
                return v___x_2025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_containsThenInsertIfNew(
    mut v_00_u03b1_2032_: *mut LeanObject,
    mut v_00_u03b2_2033_: *mut LeanObject,
    mut v_x_2034_: *mut LeanObject,
    mut v_x_2035_: *mut LeanObject,
    mut v_inst_2036_: *mut LeanObject,
    mut v_inst_2037_: *mut LeanObject,
    mut v_m_2038_: *mut LeanObject,
    mut v_a_2039_: *mut LeanObject,
    mut v_b_2040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v_val_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_unused_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2041_ = lean_ctor_get(v_m_2038_, 0);
                v_buckets_2042_ = lean_ctor_get(v_m_2038_, 1);
                v___x_2043_ = lean_array_get_size(v_buckets_2042_);
                lean_inc_ref(v_x_2035_);
                lean_inc_n(v_a_2039_, 2);
                v___x_2044_ = lean_apply_1(v_x_2035_, v_a_2039_);
                v___x_2045_ = 32u64;
                v___x_2046_ = lean_unbox_uint64(v___x_2044_);
                v___x_2047_ = lean_uint64_shift_right(v___x_2046_, v___x_2045_);
                v___x_2048_ = lean_unbox_uint64(v___x_2044_);
                lean_dec_ref(v___x_2044_);
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
                lean_inc(v_bkt_2058_);
                v___x_2059_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_2034_,
                    v_a_2039_,
                    v_bkt_2058_,
                );
                if v___x_2059_ == 0 {
                    lean_inc_ref(v_buckets_2042_);
                    lean_inc(v_size_2041_);
                    v_isSharedCheck_2084_ = (!lean_is_exclusive(v_m_2038_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v_unused_2085_ = lean_ctor_get(v_m_2038_, 1);
                        lean_dec(v_unused_2085_);
                        v_unused_2086_ = lean_ctor_get(v_m_2038_, 0);
                        lean_dec(v_unused_2086_);
                        v___x_2061_ = v_m_2038_;
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2038_);
                        v___x_2061_ = lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2040_);
                    lean_dec(v_a_2039_);
                    lean_dec_ref(v_x_2035_);
                    v___x_2087_ = lean_box((v___x_2059_) as usize);
                    v___x_2088_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                    lean_ctor_set(v___x_2088_, 1, v_m_2038_);
                    return v___x_2088_;
                }
            }
            1 => {
                v___x_2063_ = lean_unsigned_to_nat(1);
                v_size_x27_2064_ = lean_nat_add(v_size_2041_, v___x_2063_);
                lean_dec(v_size_2041_);
                lean_inc(v_bkt_2058_);
                v___x_2065_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2065_, 0, v_a_2039_);
                lean_ctor_set(v___x_2065_, 1, v_b_2040_);
                lean_ctor_set(v___x_2065_, 2, v_bkt_2058_);
                v_buckets_x27_2066_ = lean_array_uset(v_buckets_2042_, v___x_2057_, v___x_2065_);
                v___x_2067_ = lean_unsigned_to_nat(4);
                v___x_2068_ = lean_nat_mul(v_size_x27_2064_, v___x_2067_);
                v___x_2069_ = lean_unsigned_to_nat(3);
                v___x_2070_ = lean_nat_div(v___x_2068_, v___x_2069_);
                lean_dec(v___x_2068_);
                v___x_2071_ = lean_array_get_size(v_buckets_x27_2066_);
                v___x_2072_ = lean_nat_dec_le(v___x_2070_, v___x_2071_);
                lean_dec(v___x_2070_);
                if v___x_2072_ == 0 {
                    v_val_2073_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2035_,
                        v_buckets_x27_2066_,
                    );
                    if v_isShared_2062_ == 0 {
                        lean_ctor_set(v___x_2061_, 1, v_val_2073_);
                        lean_ctor_set(v___x_2061_, 0, v_size_x27_2064_);
                        v___x_2075_ = v___x_2061_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_size_x27_2064_);
                        lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_val_2073_);
                        v___x_2075_ = v_reuseFailAlloc_2078_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2035_);
                    if v_isShared_2062_ == 0 {
                        lean_ctor_set(v___x_2061_, 1, v_buckets_x27_2066_);
                        lean_ctor_set(v___x_2061_, 0, v_size_x27_2064_);
                        v___x_2080_ = v___x_2061_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_size_x27_2064_);
                        lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_buckets_x27_2066_);
                        v___x_2080_ = v_reuseFailAlloc_2083_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2076_ = lean_box((v___x_2059_) as usize);
                v___x_2077_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2077_, 0, v___x_2076_);
                lean_ctor_set(v___x_2077_, 1, v___x_2075_);
                return v___x_2077_;
            }
            3 => {
                v___x_2081_ = lean_box((v___x_2059_) as usize);
                v___x_2082_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2082_, 0, v___x_2081_);
                lean_ctor_set(v___x_2082_, 1, v___x_2080_);
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getThenInsertIfNew_x3f___redArg(
    mut v_x_2089_: *mut LeanObject,
    mut v_x_2090_: *mut LeanObject,
    mut v_m_2091_: *mut LeanObject,
    mut v_a_2092_: *mut LeanObject,
    mut v_b_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: u8 = 0;
    let mut v_val_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2094_ = lean_ctor_get(v_m_2091_, 0);
                v_buckets_2095_ = lean_ctor_get(v_m_2091_, 1);
                v___x_2096_ = lean_array_get_size(v_buckets_2095_);
                lean_inc_ref(v_x_2090_);
                lean_inc_n(v_a_2092_, 2);
                v___x_2097_ = lean_apply_1(v_x_2090_, v_a_2092_);
                v___x_2098_ = 32u64;
                v___x_2099_ = lean_unbox_uint64(v___x_2097_);
                v___x_2100_ = lean_uint64_shift_right(v___x_2099_, v___x_2098_);
                v___x_2101_ = lean_unbox_uint64(v___x_2097_);
                lean_dec_ref(v___x_2097_);
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
                lean_inc(v_bkt_2111_);
                v___x_2112_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_x_2089_,
                    v_a_2092_,
                    v_bkt_2111_,
                );
                if lean_obj_tag(v___x_2112_) == 0 {
                    lean_inc_ref(v_buckets_2095_);
                    lean_inc(v_size_2094_);
                    v_isSharedCheck_2135_ = (!lean_is_exclusive(v_m_2091_)) as u8;
                    if v_isSharedCheck_2135_ == 0 {
                        v_unused_2136_ = lean_ctor_get(v_m_2091_, 1);
                        lean_dec(v_unused_2136_);
                        v_unused_2137_ = lean_ctor_get(v_m_2091_, 0);
                        lean_dec(v_unused_2137_);
                        v___x_2114_ = v_m_2091_;
                        v_isShared_2115_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2091_);
                        v___x_2114_ = lean_box(0);
                        v_isShared_2115_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2093_);
                    lean_dec(v_a_2092_);
                    lean_dec_ref(v_x_2090_);
                    v___x_2138_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2138_, 0, v___x_2112_);
                    lean_ctor_set(v___x_2138_, 1, v_m_2091_);
                    return v___x_2138_;
                }
            }
            1 => {
                v___x_2116_ = lean_unsigned_to_nat(1);
                v_size_x27_2117_ = lean_nat_add(v_size_2094_, v___x_2116_);
                lean_dec(v_size_2094_);
                lean_inc(v_bkt_2111_);
                v___x_2118_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2118_, 0, v_a_2092_);
                lean_ctor_set(v___x_2118_, 1, v_b_2093_);
                lean_ctor_set(v___x_2118_, 2, v_bkt_2111_);
                v_buckets_x27_2119_ = lean_array_uset(v_buckets_2095_, v___x_2110_, v___x_2118_);
                v___x_2120_ = lean_unsigned_to_nat(4);
                v___x_2121_ = lean_nat_mul(v_size_x27_2117_, v___x_2120_);
                v___x_2122_ = lean_unsigned_to_nat(3);
                v___x_2123_ = lean_nat_div(v___x_2121_, v___x_2122_);
                lean_dec(v___x_2121_);
                v___x_2124_ = lean_array_get_size(v_buckets_x27_2119_);
                v___x_2125_ = lean_nat_dec_le(v___x_2123_, v___x_2124_);
                lean_dec(v___x_2123_);
                if v___x_2125_ == 0 {
                    v_val_2126_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2090_,
                        v_buckets_x27_2119_,
                    );
                    if v_isShared_2115_ == 0 {
                        lean_ctor_set(v___x_2114_, 1, v_val_2126_);
                        lean_ctor_set(v___x_2114_, 0, v_size_x27_2117_);
                        v___x_2128_ = v___x_2114_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_size_x27_2117_);
                        lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_val_2126_);
                        v___x_2128_ = v_reuseFailAlloc_2130_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2090_);
                    if v_isShared_2115_ == 0 {
                        lean_ctor_set(v___x_2114_, 1, v_buckets_x27_2119_);
                        lean_ctor_set(v___x_2114_, 0, v_size_x27_2117_);
                        v___x_2132_ = v___x_2114_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_size_x27_2117_);
                        lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_buckets_x27_2119_);
                        v___x_2132_ = v_reuseFailAlloc_2134_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2129_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2129_, 0, v___x_2112_);
                lean_ctor_set(v___x_2129_, 1, v___x_2128_);
                return v___x_2129_;
            }
            3 => {
                v___x_2133_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2133_, 0, v___x_2112_);
                lean_ctor_set(v___x_2133_, 1, v___x_2132_);
                return v___x_2133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2139_: *mut LeanObject,
    mut v_00_u03b2_2140_: *mut LeanObject,
    mut v_x_2141_: *mut LeanObject,
    mut v_x_2142_: *mut LeanObject,
    mut v_inst_2143_: *mut LeanObject,
    mut v_m_2144_: *mut LeanObject,
    mut v_a_2145_: *mut LeanObject,
    mut v_b_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    let mut v_val_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_unused_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2147_ = lean_ctor_get(v_m_2144_, 0);
                v_buckets_2148_ = lean_ctor_get(v_m_2144_, 1);
                v___x_2149_ = lean_array_get_size(v_buckets_2148_);
                lean_inc_ref(v_x_2142_);
                lean_inc_n(v_a_2145_, 2);
                v___x_2150_ = lean_apply_1(v_x_2142_, v_a_2145_);
                v___x_2151_ = 32u64;
                v___x_2152_ = lean_unbox_uint64(v___x_2150_);
                v___x_2153_ = lean_uint64_shift_right(v___x_2152_, v___x_2151_);
                v___x_2154_ = lean_unbox_uint64(v___x_2150_);
                lean_dec_ref(v___x_2150_);
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
                lean_inc(v_bkt_2164_);
                v___x_2165_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_x_2141_,
                    v_a_2145_,
                    v_bkt_2164_,
                );
                if lean_obj_tag(v___x_2165_) == 0 {
                    lean_inc_ref(v_buckets_2148_);
                    lean_inc(v_size_2147_);
                    v_isSharedCheck_2188_ = (!lean_is_exclusive(v_m_2144_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v_unused_2189_ = lean_ctor_get(v_m_2144_, 1);
                        lean_dec(v_unused_2189_);
                        v_unused_2190_ = lean_ctor_get(v_m_2144_, 0);
                        lean_dec(v_unused_2190_);
                        v___x_2167_ = v_m_2144_;
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2144_);
                        v___x_2167_ = lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2146_);
                    lean_dec(v_a_2145_);
                    lean_dec_ref(v_x_2142_);
                    v___x_2191_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2191_, 0, v___x_2165_);
                    lean_ctor_set(v___x_2191_, 1, v_m_2144_);
                    return v___x_2191_;
                }
            }
            1 => {
                v___x_2169_ = lean_unsigned_to_nat(1);
                v_size_x27_2170_ = lean_nat_add(v_size_2147_, v___x_2169_);
                lean_dec(v_size_2147_);
                lean_inc(v_bkt_2164_);
                v___x_2171_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2171_, 0, v_a_2145_);
                lean_ctor_set(v___x_2171_, 1, v_b_2146_);
                lean_ctor_set(v___x_2171_, 2, v_bkt_2164_);
                v_buckets_x27_2172_ = lean_array_uset(v_buckets_2148_, v___x_2163_, v___x_2171_);
                v___x_2173_ = lean_unsigned_to_nat(4);
                v___x_2174_ = lean_nat_mul(v_size_x27_2170_, v___x_2173_);
                v___x_2175_ = lean_unsigned_to_nat(3);
                v___x_2176_ = lean_nat_div(v___x_2174_, v___x_2175_);
                lean_dec(v___x_2174_);
                v___x_2177_ = lean_array_get_size(v_buckets_x27_2172_);
                v___x_2178_ = lean_nat_dec_le(v___x_2176_, v___x_2177_);
                lean_dec(v___x_2176_);
                if v___x_2178_ == 0 {
                    v_val_2179_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2142_,
                        v_buckets_x27_2172_,
                    );
                    if v_isShared_2168_ == 0 {
                        lean_ctor_set(v___x_2167_, 1, v_val_2179_);
                        lean_ctor_set(v___x_2167_, 0, v_size_x27_2170_);
                        v___x_2181_ = v___x_2167_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_size_x27_2170_);
                        lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_val_2179_);
                        v___x_2181_ = v_reuseFailAlloc_2183_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2142_);
                    if v_isShared_2168_ == 0 {
                        lean_ctor_set(v___x_2167_, 1, v_buckets_x27_2172_);
                        lean_ctor_set(v___x_2167_, 0, v_size_x27_2170_);
                        v___x_2185_ = v___x_2167_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_size_x27_2170_);
                        lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_buckets_x27_2172_);
                        v___x_2185_ = v_reuseFailAlloc_2187_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2182_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2182_, 0, v___x_2165_);
                lean_ctor_set(v___x_2182_, 1, v___x_2181_);
                return v___x_2182_;
            }
            3 => {
                v___x_2186_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2186_, 0, v___x_2165_);
                lean_ctor_set(v___x_2186_, 1, v___x_2185_);
                return v___x_2186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___redArg(
    mut v_x_2192_: *mut LeanObject,
    mut v_x_2193_: *mut LeanObject,
    mut v_m_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_x_2192_, v_x_2193_, v_m_2194_, v_a_2195_,
    );
    return v___x_2196_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___redArg___boxed(
    mut v_x_2197_: *mut LeanObject,
    mut v_x_2198_: *mut LeanObject,
    mut v_m_2199_: *mut LeanObject,
    mut v_a_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2201_: *mut LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Std_ExtDHashMap_get_x3f___redArg(v_x_2197_, v_x_2198_, v_m_2199_, v_a_2200_);
    lean_dec(v_m_2199_);
    return v_res_2201_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f(
    mut v_00_u03b1_2202_: *mut LeanObject,
    mut v_00_u03b2_2203_: *mut LeanObject,
    mut v_x_2204_: *mut LeanObject,
    mut v_x_2205_: *mut LeanObject,
    mut v_inst_2206_: *mut LeanObject,
    mut v_m_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    v___x_2209_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_x_2204_, v_x_2205_, v_m_2207_, v_a_2208_,
    );
    return v___x_2209_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x3f___boxed(
    mut v_00_u03b1_2210_: *mut LeanObject,
    mut v_00_u03b2_2211_: *mut LeanObject,
    mut v_x_2212_: *mut LeanObject,
    mut v_x_2213_: *mut LeanObject,
    mut v_inst_2214_: *mut LeanObject,
    mut v_m_2215_: *mut LeanObject,
    mut v_a_2216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2217_: *mut LeanObject = core::ptr::null_mut();
    v_res_2217_ = l_Std_ExtDHashMap_get_x3f(
        v_00_u03b1_2210_,
        v_00_u03b2_2211_,
        v_x_2212_,
        v_x_2213_,
        v_inst_2214_,
        v_m_2215_,
        v_a_2216_,
    );
    lean_dec(v_m_2215_);
    return v_res_2217_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___redArg(
    mut v_x_2218_: *mut LeanObject,
    mut v_x_2219_: *mut LeanObject,
    mut v_m_2220_: *mut LeanObject,
    mut v_a_2221_: *mut LeanObject,
) -> u8 {
    let mut v___x_2222_: u8 = 0;
    v___x_2222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2218_, v_x_2219_, v_m_2220_, v_a_2221_,
    );
    return v___x_2222_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___redArg___boxed(
    mut v_x_2223_: *mut LeanObject,
    mut v_x_2224_: *mut LeanObject,
    mut v_m_2225_: *mut LeanObject,
    mut v_a_2226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2227_: u8 = 0;
    let mut v_r_2228_: *mut LeanObject = core::ptr::null_mut();
    v_res_2227_ = l_Std_ExtDHashMap_contains___redArg(v_x_2223_, v_x_2224_, v_m_2225_, v_a_2226_);
    lean_dec(v_m_2225_);
    v_r_2228_ = lean_box((v_res_2227_) as usize);
    return v_r_2228_;
}
pub unsafe fn l_Std_ExtDHashMap_contains(
    mut v_00_u03b1_2229_: *mut LeanObject,
    mut v_00_u03b2_2230_: *mut LeanObject,
    mut v_x_2231_: *mut LeanObject,
    mut v_x_2232_: *mut LeanObject,
    mut v_inst_2233_: *mut LeanObject,
    mut v_inst_2234_: *mut LeanObject,
    mut v_m_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
) -> u8 {
    let mut v___x_2237_: u8 = 0;
    v___x_2237_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2231_, v_x_2232_, v_m_2235_, v_a_2236_,
    );
    return v___x_2237_;
}
pub unsafe fn l_Std_ExtDHashMap_contains___boxed(
    mut v_00_u03b1_2238_: *mut LeanObject,
    mut v_00_u03b2_2239_: *mut LeanObject,
    mut v_x_2240_: *mut LeanObject,
    mut v_x_2241_: *mut LeanObject,
    mut v_inst_2242_: *mut LeanObject,
    mut v_inst_2243_: *mut LeanObject,
    mut v_m_2244_: *mut LeanObject,
    mut v_a_2245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2246_: u8 = 0;
    let mut v_r_2247_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2244_);
    v_r_2247_ = lean_box((v_res_2246_) as usize);
    return v_r_2247_;
}
pub unsafe fn l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2248_: *mut LeanObject,
    mut v_00_u03b2_2249_: *mut LeanObject,
    mut v_x_2250_: *mut LeanObject,
    mut v_x_2251_: *mut LeanObject,
    mut v_inst_2252_: *mut LeanObject,
    mut v_inst_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    v___x_2254_ = lean_box(0);
    return v___x_2254_;
}
pub unsafe fn l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(
    mut v_00_u03b1_2255_: *mut LeanObject,
    mut v_00_u03b2_2256_: *mut LeanObject,
    mut v_x_2257_: *mut LeanObject,
    mut v_x_2258_: *mut LeanObject,
    mut v_inst_2259_: *mut LeanObject,
    mut v_inst_2260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2261_: *mut LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(
        v_00_u03b1_2255_,
        v_00_u03b2_2256_,
        v_x_2257_,
        v_x_2258_,
        v_inst_2259_,
        v_inst_2260_,
    );
    lean_dec_ref(v_x_2258_);
    lean_dec_ref(v_x_2257_);
    return v_res_2261_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___redArg(
    mut v_x_2262_: *mut LeanObject,
    mut v_x_2263_: *mut LeanObject,
    mut v_m_2264_: *mut LeanObject,
    mut v_a_2265_: *mut LeanObject,
) -> u8 {
    let mut v___x_2266_: u8 = 0;
    v___x_2266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2262_, v_x_2263_, v_m_2264_, v_a_2265_,
    );
    return v___x_2266_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___redArg___boxed(
    mut v_x_2267_: *mut LeanObject,
    mut v_x_2268_: *mut LeanObject,
    mut v_m_2269_: *mut LeanObject,
    mut v_a_2270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2271_: u8 = 0;
    let mut v_r_2272_: *mut LeanObject = core::ptr::null_mut();
    v_res_2271_ =
        l_Std_ExtDHashMap_instDecidableMem___redArg(v_x_2267_, v_x_2268_, v_m_2269_, v_a_2270_);
    lean_dec(v_m_2269_);
    v_r_2272_ = lean_box((v_res_2271_) as usize);
    return v_r_2272_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem(
    mut v_00_u03b1_2273_: *mut LeanObject,
    mut v_00_u03b2_2274_: *mut LeanObject,
    mut v_x_2275_: *mut LeanObject,
    mut v_x_2276_: *mut LeanObject,
    mut v_inst_2277_: *mut LeanObject,
    mut v_inst_2278_: *mut LeanObject,
    mut v_m_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
) -> u8 {
    let mut v___x_2281_: u8 = 0;
    v___x_2281_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2275_, v_x_2276_, v_m_2279_, v_a_2280_,
    );
    return v___x_2281_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableMem___boxed(
    mut v_00_u03b1_2282_: *mut LeanObject,
    mut v_00_u03b2_2283_: *mut LeanObject,
    mut v_x_2284_: *mut LeanObject,
    mut v_x_2285_: *mut LeanObject,
    mut v_inst_2286_: *mut LeanObject,
    mut v_inst_2287_: *mut LeanObject,
    mut v_m_2288_: *mut LeanObject,
    mut v_a_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2290_: u8 = 0;
    let mut v_r_2291_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2288_);
    v_r_2291_ = lean_box((v_res_2290_) as usize);
    return v_r_2291_;
}
pub unsafe fn l_Std_ExtDHashMap_get___redArg(
    mut v_x_2292_: *mut LeanObject,
    mut v_x_2293_: *mut LeanObject,
    mut v_m_2294_: *mut LeanObject,
    mut v_a_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    v___x_2296_ =
        l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_2292_, v_x_2293_, v_m_2294_, v_a_2295_);
    return v___x_2296_;
}
pub unsafe fn l_Std_ExtDHashMap_get___redArg___boxed(
    mut v_x_2297_: *mut LeanObject,
    mut v_x_2298_: *mut LeanObject,
    mut v_m_2299_: *mut LeanObject,
    mut v_a_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2301_: *mut LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Std_ExtDHashMap_get___redArg(v_x_2297_, v_x_2298_, v_m_2299_, v_a_2300_);
    lean_dec(v_m_2299_);
    return v_res_2301_;
}
pub unsafe fn l_Std_ExtDHashMap_get(
    mut v_00_u03b1_2302_: *mut LeanObject,
    mut v_00_u03b2_2303_: *mut LeanObject,
    mut v_x_2304_: *mut LeanObject,
    mut v_x_2305_: *mut LeanObject,
    mut v_inst_2306_: *mut LeanObject,
    mut v_m_2307_: *mut LeanObject,
    mut v_a_2308_: *mut LeanObject,
    mut v_h_2309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    v___x_2310_ =
        l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_2304_, v_x_2305_, v_m_2307_, v_a_2308_);
    return v___x_2310_;
}
pub unsafe fn l_Std_ExtDHashMap_get___boxed(
    mut v_00_u03b1_2311_: *mut LeanObject,
    mut v_00_u03b2_2312_: *mut LeanObject,
    mut v_x_2313_: *mut LeanObject,
    mut v_x_2314_: *mut LeanObject,
    mut v_inst_2315_: *mut LeanObject,
    mut v_m_2316_: *mut LeanObject,
    mut v_a_2317_: *mut LeanObject,
    mut v_h_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2319_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2316_);
    return v_res_2319_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x21___redArg(
    mut v_x_2320_: *mut LeanObject,
    mut v_x_2321_: *mut LeanObject,
    mut v_m_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
    mut v_inst_2324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2326_: *mut LeanObject,
    mut v_x_2327_: *mut LeanObject,
    mut v_m_2328_: *mut LeanObject,
    mut v_a_2329_: *mut LeanObject,
    mut v_inst_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2331_: *mut LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Std_ExtDHashMap_get_x21___redArg(
        v_x_2326_,
        v_x_2327_,
        v_m_2328_,
        v_a_2329_,
        v_inst_2330_,
    );
    lean_dec(v_inst_2330_);
    lean_dec(v_m_2328_);
    return v_res_2331_;
}
pub unsafe fn l_Std_ExtDHashMap_get_x21(
    mut v_00_u03b1_2332_: *mut LeanObject,
    mut v_00_u03b2_2333_: *mut LeanObject,
    mut v_x_2334_: *mut LeanObject,
    mut v_x_2335_: *mut LeanObject,
    mut v_inst_2336_: *mut LeanObject,
    mut v_m_2337_: *mut LeanObject,
    mut v_a_2338_: *mut LeanObject,
    mut v_inst_2339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2341_: *mut LeanObject,
    mut v_00_u03b2_2342_: *mut LeanObject,
    mut v_x_2343_: *mut LeanObject,
    mut v_x_2344_: *mut LeanObject,
    mut v_inst_2345_: *mut LeanObject,
    mut v_m_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
    mut v_inst_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2349_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2348_);
    lean_dec(v_m_2346_);
    return v_res_2349_;
}
pub unsafe fn l_Std_ExtDHashMap_getD___redArg(
    mut v_x_2350_: *mut LeanObject,
    mut v_x_2351_: *mut LeanObject,
    mut v_m_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_fallback_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2356_: *mut LeanObject,
    mut v_x_2357_: *mut LeanObject,
    mut v_m_2358_: *mut LeanObject,
    mut v_a_2359_: *mut LeanObject,
    mut v_fallback_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2361_: *mut LeanObject = core::ptr::null_mut();
    v_res_2361_ = l_Std_ExtDHashMap_getD___redArg(
        v_x_2356_,
        v_x_2357_,
        v_m_2358_,
        v_a_2359_,
        v_fallback_2360_,
    );
    lean_dec(v_fallback_2360_);
    lean_dec(v_m_2358_);
    return v_res_2361_;
}
pub unsafe fn l_Std_ExtDHashMap_getD(
    mut v_00_u03b1_2362_: *mut LeanObject,
    mut v_00_u03b2_2363_: *mut LeanObject,
    mut v_x_2364_: *mut LeanObject,
    mut v_x_2365_: *mut LeanObject,
    mut v_inst_2366_: *mut LeanObject,
    mut v_m_2367_: *mut LeanObject,
    mut v_a_2368_: *mut LeanObject,
    mut v_fallback_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2371_: *mut LeanObject,
    mut v_00_u03b2_2372_: *mut LeanObject,
    mut v_x_2373_: *mut LeanObject,
    mut v_x_2374_: *mut LeanObject,
    mut v_inst_2375_: *mut LeanObject,
    mut v_m_2376_: *mut LeanObject,
    mut v_a_2377_: *mut LeanObject,
    mut v_fallback_2378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2379_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_fallback_2378_);
    lean_dec(v_m_2376_);
    return v_res_2379_;
}
pub unsafe fn l_Std_ExtDHashMap_erase___redArg(
    mut v_x_2380_: *mut LeanObject,
    mut v_x_2381_: *mut LeanObject,
    mut v_m_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_2380_, v_x_2381_, v_m_2382_, v_a_2383_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Std_ExtDHashMap_erase(
    mut v_00_u03b1_2385_: *mut LeanObject,
    mut v_00_u03b2_2386_: *mut LeanObject,
    mut v_x_2387_: *mut LeanObject,
    mut v_x_2388_: *mut LeanObject,
    mut v_inst_2389_: *mut LeanObject,
    mut v_inst_2390_: *mut LeanObject,
    mut v_m_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_2387_, v_x_2388_, v_m_2391_, v_a_2392_,
    );
    return v___x_2393_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___redArg(
    mut v_x_2394_: *mut LeanObject,
    mut v_x_2395_: *mut LeanObject,
    mut v_m_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    v___x_2398_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_2394_, v_x_2395_, v_m_2396_, v_a_2397_,
    );
    return v___x_2398_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___redArg___boxed(
    mut v_x_2399_: *mut LeanObject,
    mut v_x_2400_: *mut LeanObject,
    mut v_m_2401_: *mut LeanObject,
    mut v_a_2402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2403_: *mut LeanObject = core::ptr::null_mut();
    v_res_2403_ =
        l_Std_ExtDHashMap_Const_get_x3f___redArg(v_x_2399_, v_x_2400_, v_m_2401_, v_a_2402_);
    lean_dec(v_m_2401_);
    return v_res_2403_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f(
    mut v_00_u03b1_2404_: *mut LeanObject,
    mut v_x_2405_: *mut LeanObject,
    mut v_x_2406_: *mut LeanObject,
    mut v_00_u03b2_2407_: *mut LeanObject,
    mut v_inst_2408_: *mut LeanObject,
    mut v_inst_2409_: *mut LeanObject,
    mut v_m_2410_: *mut LeanObject,
    mut v_a_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_2405_, v_x_2406_, v_m_2410_, v_a_2411_,
    );
    return v___x_2412_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x3f___boxed(
    mut v_00_u03b1_2413_: *mut LeanObject,
    mut v_x_2414_: *mut LeanObject,
    mut v_x_2415_: *mut LeanObject,
    mut v_00_u03b2_2416_: *mut LeanObject,
    mut v_inst_2417_: *mut LeanObject,
    mut v_inst_2418_: *mut LeanObject,
    mut v_m_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2421_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2419_);
    return v_res_2421_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___redArg(
    mut v_x_2422_: *mut LeanObject,
    mut v_x_2423_: *mut LeanObject,
    mut v_m_2424_: *mut LeanObject,
    mut v_a_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    v___x_2426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_2422_, v_x_2423_, v_m_2424_, v_a_2425_,
    );
    return v___x_2426_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___redArg___boxed(
    mut v_x_2427_: *mut LeanObject,
    mut v_x_2428_: *mut LeanObject,
    mut v_m_2429_: *mut LeanObject,
    mut v_a_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2431_: *mut LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Std_ExtDHashMap_Const_get___redArg(v_x_2427_, v_x_2428_, v_m_2429_, v_a_2430_);
    lean_dec(v_m_2429_);
    return v_res_2431_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get(
    mut v_00_u03b1_2432_: *mut LeanObject,
    mut v_x_2433_: *mut LeanObject,
    mut v_x_2434_: *mut LeanObject,
    mut v_00_u03b2_2435_: *mut LeanObject,
    mut v_inst_2436_: *mut LeanObject,
    mut v_inst_2437_: *mut LeanObject,
    mut v_m_2438_: *mut LeanObject,
    mut v_a_2439_: *mut LeanObject,
    mut v_h_2440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_2433_, v_x_2434_, v_m_2438_, v_a_2439_,
    );
    return v___x_2441_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get___boxed(
    mut v_00_u03b1_2442_: *mut LeanObject,
    mut v_x_2443_: *mut LeanObject,
    mut v_x_2444_: *mut LeanObject,
    mut v_00_u03b2_2445_: *mut LeanObject,
    mut v_inst_2446_: *mut LeanObject,
    mut v_inst_2447_: *mut LeanObject,
    mut v_m_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
    mut v_h_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2451_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2448_);
    return v_res_2451_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getD___redArg(
    mut v_x_2452_: *mut LeanObject,
    mut v_x_2453_: *mut LeanObject,
    mut v_m_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
    mut v_fallback_2456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2458_: *mut LeanObject,
    mut v_x_2459_: *mut LeanObject,
    mut v_m_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
    mut v_fallback_2462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2463_: *mut LeanObject = core::ptr::null_mut();
    v_res_2463_ = l_Std_ExtDHashMap_Const_getD___redArg(
        v_x_2458_,
        v_x_2459_,
        v_m_2460_,
        v_a_2461_,
        v_fallback_2462_,
    );
    lean_dec(v_fallback_2462_);
    lean_dec(v_m_2460_);
    return v_res_2463_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getD(
    mut v_00_u03b1_2464_: *mut LeanObject,
    mut v_x_2465_: *mut LeanObject,
    mut v_x_2466_: *mut LeanObject,
    mut v_00_u03b2_2467_: *mut LeanObject,
    mut v_inst_2468_: *mut LeanObject,
    mut v_inst_2469_: *mut LeanObject,
    mut v_m_2470_: *mut LeanObject,
    mut v_a_2471_: *mut LeanObject,
    mut v_fallback_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2474_: *mut LeanObject,
    mut v_x_2475_: *mut LeanObject,
    mut v_x_2476_: *mut LeanObject,
    mut v_00_u03b2_2477_: *mut LeanObject,
    mut v_inst_2478_: *mut LeanObject,
    mut v_inst_2479_: *mut LeanObject,
    mut v_m_2480_: *mut LeanObject,
    mut v_a_2481_: *mut LeanObject,
    mut v_fallback_2482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2483_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_fallback_2482_);
    lean_dec(v_m_2480_);
    return v_res_2483_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x21___redArg(
    mut v_x_2484_: *mut LeanObject,
    mut v_x_2485_: *mut LeanObject,
    mut v_inst_2486_: *mut LeanObject,
    mut v_m_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2490_: *mut LeanObject,
    mut v_x_2491_: *mut LeanObject,
    mut v_inst_2492_: *mut LeanObject,
    mut v_m_2493_: *mut LeanObject,
    mut v_a_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2495_: *mut LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_Std_ExtDHashMap_Const_get_x21___redArg(
        v_x_2490_,
        v_x_2491_,
        v_inst_2492_,
        v_m_2493_,
        v_a_2494_,
    );
    lean_dec(v_m_2493_);
    lean_dec(v_inst_2492_);
    return v_res_2495_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_get_x21(
    mut v_00_u03b1_2496_: *mut LeanObject,
    mut v_x_2497_: *mut LeanObject,
    mut v_x_2498_: *mut LeanObject,
    mut v_00_u03b2_2499_: *mut LeanObject,
    mut v_inst_2500_: *mut LeanObject,
    mut v_inst_2501_: *mut LeanObject,
    mut v_inst_2502_: *mut LeanObject,
    mut v_m_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2506_: *mut LeanObject,
    mut v_x_2507_: *mut LeanObject,
    mut v_x_2508_: *mut LeanObject,
    mut v_00_u03b2_2509_: *mut LeanObject,
    mut v_inst_2510_: *mut LeanObject,
    mut v_inst_2511_: *mut LeanObject,
    mut v_inst_2512_: *mut LeanObject,
    mut v_m_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2515_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2513_);
    lean_dec(v_inst_2512_);
    return v_res_2515_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f___redArg(
    mut v_x_2516_: *mut LeanObject,
    mut v_x_2517_: *mut LeanObject,
    mut v_m_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
    mut v_b_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v_val_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2562_: u8 = 0;
    let mut v_unused_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2521_ = lean_ctor_get(v_m_2518_, 0);
                v_buckets_2522_ = lean_ctor_get(v_m_2518_, 1);
                v___x_2523_ = lean_array_get_size(v_buckets_2522_);
                lean_inc_ref(v_x_2517_);
                lean_inc_n(v_a_2519_, 2);
                v___x_2524_ = lean_apply_1(v_x_2517_, v_a_2519_);
                v___x_2525_ = 32u64;
                v___x_2526_ = lean_unbox_uint64(v___x_2524_);
                v___x_2527_ = lean_uint64_shift_right(v___x_2526_, v___x_2525_);
                v___x_2528_ = lean_unbox_uint64(v___x_2524_);
                lean_dec_ref(v___x_2524_);
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
                lean_inc(v_bkt_2538_);
                v___x_2539_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_2516_,
                    v_a_2519_,
                    v_bkt_2538_,
                );
                if lean_obj_tag(v___x_2539_) == 0 {
                    lean_inc_ref(v_buckets_2522_);
                    lean_inc(v_size_2521_);
                    v_isSharedCheck_2562_ = (!lean_is_exclusive(v_m_2518_)) as u8;
                    if v_isSharedCheck_2562_ == 0 {
                        v_unused_2563_ = lean_ctor_get(v_m_2518_, 1);
                        lean_dec(v_unused_2563_);
                        v_unused_2564_ = lean_ctor_get(v_m_2518_, 0);
                        lean_dec(v_unused_2564_);
                        v___x_2541_ = v_m_2518_;
                        v_isShared_2542_ = v_isSharedCheck_2562_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2518_);
                        v___x_2541_ = lean_box(0);
                        v_isShared_2542_ = v_isSharedCheck_2562_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2520_);
                    lean_dec(v_a_2519_);
                    lean_dec_ref(v_x_2517_);
                    v___x_2565_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2565_, 0, v___x_2539_);
                    lean_ctor_set(v___x_2565_, 1, v_m_2518_);
                    return v___x_2565_;
                }
            }
            1 => {
                v___x_2543_ = lean_unsigned_to_nat(1);
                v_size_x27_2544_ = lean_nat_add(v_size_2521_, v___x_2543_);
                lean_dec(v_size_2521_);
                lean_inc(v_bkt_2538_);
                v___x_2545_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2545_, 0, v_a_2519_);
                lean_ctor_set(v___x_2545_, 1, v_b_2520_);
                lean_ctor_set(v___x_2545_, 2, v_bkt_2538_);
                v_buckets_x27_2546_ = lean_array_uset(v_buckets_2522_, v___x_2537_, v___x_2545_);
                v___x_2547_ = lean_unsigned_to_nat(4);
                v___x_2548_ = lean_nat_mul(v_size_x27_2544_, v___x_2547_);
                v___x_2549_ = lean_unsigned_to_nat(3);
                v___x_2550_ = lean_nat_div(v___x_2548_, v___x_2549_);
                lean_dec(v___x_2548_);
                v___x_2551_ = lean_array_get_size(v_buckets_x27_2546_);
                v___x_2552_ = lean_nat_dec_le(v___x_2550_, v___x_2551_);
                lean_dec(v___x_2550_);
                if v___x_2552_ == 0 {
                    v_val_2553_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2517_,
                        v_buckets_x27_2546_,
                    );
                    if v_isShared_2542_ == 0 {
                        lean_ctor_set(v___x_2541_, 1, v_val_2553_);
                        lean_ctor_set(v___x_2541_, 0, v_size_x27_2544_);
                        v___x_2555_ = v___x_2541_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_size_x27_2544_);
                        lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_val_2553_);
                        v___x_2555_ = v_reuseFailAlloc_2557_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2517_);
                    if v_isShared_2542_ == 0 {
                        lean_ctor_set(v___x_2541_, 1, v_buckets_x27_2546_);
                        lean_ctor_set(v___x_2541_, 0, v_size_x27_2544_);
                        v___x_2559_ = v___x_2541_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_size_x27_2544_);
                        lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_buckets_x27_2546_);
                        v___x_2559_ = v_reuseFailAlloc_2561_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2556_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2556_, 0, v___x_2539_);
                lean_ctor_set(v___x_2556_, 1, v___x_2555_);
                return v___x_2556_;
            }
            3 => {
                v___x_2560_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2560_, 0, v___x_2539_);
                lean_ctor_set(v___x_2560_, 1, v___x_2559_);
                return v___x_2560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2566_: *mut LeanObject,
    mut v_x_2567_: *mut LeanObject,
    mut v_x_2568_: *mut LeanObject,
    mut v_00_u03b2_2569_: *mut LeanObject,
    mut v_inst_2570_: *mut LeanObject,
    mut v_inst_2571_: *mut LeanObject,
    mut v_m_2572_: *mut LeanObject,
    mut v_a_2573_: *mut LeanObject,
    mut v_b_2574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut v_val_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_unused_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2575_ = lean_ctor_get(v_m_2572_, 0);
                v_buckets_2576_ = lean_ctor_get(v_m_2572_, 1);
                v___x_2577_ = lean_array_get_size(v_buckets_2576_);
                lean_inc_ref(v_x_2568_);
                lean_inc_n(v_a_2573_, 2);
                v___x_2578_ = lean_apply_1(v_x_2568_, v_a_2573_);
                v___x_2579_ = 32u64;
                v___x_2580_ = lean_unbox_uint64(v___x_2578_);
                v___x_2581_ = lean_uint64_shift_right(v___x_2580_, v___x_2579_);
                v___x_2582_ = lean_unbox_uint64(v___x_2578_);
                lean_dec_ref(v___x_2578_);
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
                lean_inc(v_bkt_2592_);
                v___x_2593_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_2567_,
                    v_a_2573_,
                    v_bkt_2592_,
                );
                if lean_obj_tag(v___x_2593_) == 0 {
                    lean_inc_ref(v_buckets_2576_);
                    lean_inc(v_size_2575_);
                    v_isSharedCheck_2616_ = (!lean_is_exclusive(v_m_2572_)) as u8;
                    if v_isSharedCheck_2616_ == 0 {
                        v_unused_2617_ = lean_ctor_get(v_m_2572_, 1);
                        lean_dec(v_unused_2617_);
                        v_unused_2618_ = lean_ctor_get(v_m_2572_, 0);
                        lean_dec(v_unused_2618_);
                        v___x_2595_ = v_m_2572_;
                        v_isShared_2596_ = v_isSharedCheck_2616_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2572_);
                        v___x_2595_ = lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2616_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2574_);
                    lean_dec(v_a_2573_);
                    lean_dec_ref(v_x_2568_);
                    v___x_2619_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2619_, 0, v___x_2593_);
                    lean_ctor_set(v___x_2619_, 1, v_m_2572_);
                    return v___x_2619_;
                }
            }
            1 => {
                v___x_2597_ = lean_unsigned_to_nat(1);
                v_size_x27_2598_ = lean_nat_add(v_size_2575_, v___x_2597_);
                lean_dec(v_size_2575_);
                lean_inc(v_bkt_2592_);
                v___x_2599_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2599_, 0, v_a_2573_);
                lean_ctor_set(v___x_2599_, 1, v_b_2574_);
                lean_ctor_set(v___x_2599_, 2, v_bkt_2592_);
                v_buckets_x27_2600_ = lean_array_uset(v_buckets_2576_, v___x_2591_, v___x_2599_);
                v___x_2601_ = lean_unsigned_to_nat(4);
                v___x_2602_ = lean_nat_mul(v_size_x27_2598_, v___x_2601_);
                v___x_2603_ = lean_unsigned_to_nat(3);
                v___x_2604_ = lean_nat_div(v___x_2602_, v___x_2603_);
                lean_dec(v___x_2602_);
                v___x_2605_ = lean_array_get_size(v_buckets_x27_2600_);
                v___x_2606_ = lean_nat_dec_le(v___x_2604_, v___x_2605_);
                lean_dec(v___x_2604_);
                if v___x_2606_ == 0 {
                    v_val_2607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2568_,
                        v_buckets_x27_2600_,
                    );
                    if v_isShared_2596_ == 0 {
                        lean_ctor_set(v___x_2595_, 1, v_val_2607_);
                        lean_ctor_set(v___x_2595_, 0, v_size_x27_2598_);
                        v___x_2609_ = v___x_2595_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_size_x27_2598_);
                        lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_val_2607_);
                        v___x_2609_ = v_reuseFailAlloc_2611_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2568_);
                    if v_isShared_2596_ == 0 {
                        lean_ctor_set(v___x_2595_, 1, v_buckets_x27_2600_);
                        lean_ctor_set(v___x_2595_, 0, v_size_x27_2598_);
                        v___x_2613_ = v___x_2595_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_size_x27_2598_);
                        lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_buckets_x27_2600_);
                        v___x_2613_ = v_reuseFailAlloc_2615_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2610_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2610_, 0, v___x_2593_);
                lean_ctor_set(v___x_2610_, 1, v___x_2609_);
                return v___x_2610_;
            }
            3 => {
                v___x_2614_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2614_, 0, v___x_2593_);
                lean_ctor_set(v___x_2614_, 1, v___x_2613_);
                return v___x_2614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___redArg(
    mut v_x_2620_: *mut LeanObject,
    mut v_x_2621_: *mut LeanObject,
    mut v_m_2622_: *mut LeanObject,
    mut v_a_2623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    v___x_2624_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_2620_, v_x_2621_, v_m_2622_, v_a_2623_,
    );
    return v___x_2624_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___redArg___boxed(
    mut v_x_2625_: *mut LeanObject,
    mut v_x_2626_: *mut LeanObject,
    mut v_m_2627_: *mut LeanObject,
    mut v_a_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2629_: *mut LeanObject = core::ptr::null_mut();
    v_res_2629_ = l_Std_ExtDHashMap_getKey_x3f___redArg(v_x_2625_, v_x_2626_, v_m_2627_, v_a_2628_);
    lean_dec(v_m_2627_);
    return v_res_2629_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f(
    mut v_00_u03b1_2630_: *mut LeanObject,
    mut v_00_u03b2_2631_: *mut LeanObject,
    mut v_x_2632_: *mut LeanObject,
    mut v_x_2633_: *mut LeanObject,
    mut v_inst_2634_: *mut LeanObject,
    mut v_inst_2635_: *mut LeanObject,
    mut v_m_2636_: *mut LeanObject,
    mut v_a_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    v___x_2638_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_2632_, v_x_2633_, v_m_2636_, v_a_2637_,
    );
    return v___x_2638_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x3f___boxed(
    mut v_00_u03b1_2639_: *mut LeanObject,
    mut v_00_u03b2_2640_: *mut LeanObject,
    mut v_x_2641_: *mut LeanObject,
    mut v_x_2642_: *mut LeanObject,
    mut v_inst_2643_: *mut LeanObject,
    mut v_inst_2644_: *mut LeanObject,
    mut v_m_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2647_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2645_);
    return v_res_2647_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___redArg(
    mut v_x_2648_: *mut LeanObject,
    mut v_x_2649_: *mut LeanObject,
    mut v_m_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_2648_, v_x_2649_, v_m_2650_, v_a_2651_,
    );
    return v___x_2652_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___redArg___boxed(
    mut v_x_2653_: *mut LeanObject,
    mut v_x_2654_: *mut LeanObject,
    mut v_m_2655_: *mut LeanObject,
    mut v_a_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2657_: *mut LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Std_ExtDHashMap_getKey___redArg(v_x_2653_, v_x_2654_, v_m_2655_, v_a_2656_);
    lean_dec(v_m_2655_);
    return v_res_2657_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey(
    mut v_00_u03b1_2658_: *mut LeanObject,
    mut v_00_u03b2_2659_: *mut LeanObject,
    mut v_x_2660_: *mut LeanObject,
    mut v_x_2661_: *mut LeanObject,
    mut v_inst_2662_: *mut LeanObject,
    mut v_inst_2663_: *mut LeanObject,
    mut v_m_2664_: *mut LeanObject,
    mut v_a_2665_: *mut LeanObject,
    mut v_h_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_2660_, v_x_2661_, v_m_2664_, v_a_2665_,
    );
    return v___x_2667_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey___boxed(
    mut v_00_u03b1_2668_: *mut LeanObject,
    mut v_00_u03b2_2669_: *mut LeanObject,
    mut v_x_2670_: *mut LeanObject,
    mut v_x_2671_: *mut LeanObject,
    mut v_inst_2672_: *mut LeanObject,
    mut v_inst_2673_: *mut LeanObject,
    mut v_m_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
    mut v_h_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2677_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2674_);
    return v_res_2677_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x21___redArg(
    mut v_x_2678_: *mut LeanObject,
    mut v_x_2679_: *mut LeanObject,
    mut v_inst_2680_: *mut LeanObject,
    mut v_m_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2684_: *mut LeanObject,
    mut v_x_2685_: *mut LeanObject,
    mut v_inst_2686_: *mut LeanObject,
    mut v_m_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2689_: *mut LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Std_ExtDHashMap_getKey_x21___redArg(
        v_x_2684_,
        v_x_2685_,
        v_inst_2686_,
        v_m_2687_,
        v_a_2688_,
    );
    lean_dec(v_m_2687_);
    lean_dec(v_inst_2686_);
    return v_res_2689_;
}
pub unsafe fn l_Std_ExtDHashMap_getKey_x21(
    mut v_00_u03b1_2690_: *mut LeanObject,
    mut v_00_u03b2_2691_: *mut LeanObject,
    mut v_x_2692_: *mut LeanObject,
    mut v_x_2693_: *mut LeanObject,
    mut v_inst_2694_: *mut LeanObject,
    mut v_inst_2695_: *mut LeanObject,
    mut v_inst_2696_: *mut LeanObject,
    mut v_m_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2700_: *mut LeanObject,
    mut v_00_u03b2_2701_: *mut LeanObject,
    mut v_x_2702_: *mut LeanObject,
    mut v_x_2703_: *mut LeanObject,
    mut v_inst_2704_: *mut LeanObject,
    mut v_inst_2705_: *mut LeanObject,
    mut v_inst_2706_: *mut LeanObject,
    mut v_m_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2709_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_m_2707_);
    lean_dec(v_inst_2706_);
    return v_res_2709_;
}
pub unsafe fn l_Std_ExtDHashMap_getKeyD___redArg(
    mut v_x_2710_: *mut LeanObject,
    mut v_x_2711_: *mut LeanObject,
    mut v_m_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_fallback_2714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2716_: *mut LeanObject,
    mut v_x_2717_: *mut LeanObject,
    mut v_m_2718_: *mut LeanObject,
    mut v_a_2719_: *mut LeanObject,
    mut v_fallback_2720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2721_: *mut LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_Std_ExtDHashMap_getKeyD___redArg(
        v_x_2716_,
        v_x_2717_,
        v_m_2718_,
        v_a_2719_,
        v_fallback_2720_,
    );
    lean_dec(v_fallback_2720_);
    lean_dec(v_m_2718_);
    return v_res_2721_;
}
pub unsafe fn l_Std_ExtDHashMap_getKeyD(
    mut v_00_u03b1_2722_: *mut LeanObject,
    mut v_00_u03b2_2723_: *mut LeanObject,
    mut v_x_2724_: *mut LeanObject,
    mut v_x_2725_: *mut LeanObject,
    mut v_inst_2726_: *mut LeanObject,
    mut v_inst_2727_: *mut LeanObject,
    mut v_m_2728_: *mut LeanObject,
    mut v_a_2729_: *mut LeanObject,
    mut v_fallback_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2732_: *mut LeanObject,
    mut v_00_u03b2_2733_: *mut LeanObject,
    mut v_x_2734_: *mut LeanObject,
    mut v_x_2735_: *mut LeanObject,
    mut v_inst_2736_: *mut LeanObject,
    mut v_inst_2737_: *mut LeanObject,
    mut v_m_2738_: *mut LeanObject,
    mut v_a_2739_: *mut LeanObject,
    mut v_fallback_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2741_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_fallback_2740_);
    lean_dec(v_m_2738_);
    return v_res_2741_;
}
pub unsafe fn l_Std_ExtDHashMap_size___redArg(mut v_m_2742_: *mut LeanObject) -> *mut LeanObject {
    let mut v_size_2743_: *mut LeanObject = core::ptr::null_mut();
    v_size_2743_ = lean_ctor_get(v_m_2742_, 0);
    lean_inc(v_size_2743_);
    return v_size_2743_;
}
pub unsafe fn l_Std_ExtDHashMap_size___redArg___boxed(
    mut v_m_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2745_: *mut LeanObject = core::ptr::null_mut();
    v_res_2745_ = l_Std_ExtDHashMap_size___redArg(v_m_2744_);
    lean_dec(v_m_2744_);
    return v_res_2745_;
}
pub unsafe fn l_Std_ExtDHashMap_size(
    mut v_00_u03b1_2746_: *mut LeanObject,
    mut v_00_u03b2_2747_: *mut LeanObject,
    mut v_x_2748_: *mut LeanObject,
    mut v_x_2749_: *mut LeanObject,
    mut v_inst_2750_: *mut LeanObject,
    mut v_inst_2751_: *mut LeanObject,
    mut v_m_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2753_: *mut LeanObject = core::ptr::null_mut();
    v_size_2753_ = lean_ctor_get(v_m_2752_, 0);
    lean_inc(v_size_2753_);
    return v_size_2753_;
}
pub unsafe fn l_Std_ExtDHashMap_size___boxed(
    mut v_00_u03b1_2754_: *mut LeanObject,
    mut v_00_u03b2_2755_: *mut LeanObject,
    mut v_x_2756_: *mut LeanObject,
    mut v_x_2757_: *mut LeanObject,
    mut v_inst_2758_: *mut LeanObject,
    mut v_inst_2759_: *mut LeanObject,
    mut v_m_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2761_: *mut LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_Std_ExtDHashMap_size(
        v_00_u03b1_2754_,
        v_00_u03b2_2755_,
        v_x_2756_,
        v_x_2757_,
        v_inst_2758_,
        v_inst_2759_,
        v_m_2760_,
    );
    lean_dec(v_m_2760_);
    lean_dec_ref(v_x_2757_);
    lean_dec_ref(v_x_2756_);
    return v_res_2761_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___redArg(mut v_m_2762_: *mut LeanObject) -> u8 {
    let mut v_size_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    v_size_2763_ = lean_ctor_get(v_m_2762_, 0);
    v___x_2764_ = lean_unsigned_to_nat(0);
    v___x_2765_ = lean_nat_dec_eq(v_size_2763_, v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___redArg___boxed(
    mut v_m_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2767_: u8 = 0;
    let mut v_r_2768_: *mut LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Std_ExtDHashMap_isEmpty___redArg(v_m_2766_);
    lean_dec(v_m_2766_);
    v_r_2768_ = lean_box((v_res_2767_) as usize);
    return v_r_2768_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty(
    mut v_00_u03b1_2769_: *mut LeanObject,
    mut v_00_u03b2_2770_: *mut LeanObject,
    mut v_x_2771_: *mut LeanObject,
    mut v_x_2772_: *mut LeanObject,
    mut v_inst_2773_: *mut LeanObject,
    mut v_inst_2774_: *mut LeanObject,
    mut v_m_2775_: *mut LeanObject,
) -> u8 {
    let mut v_size_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    v_size_2776_ = lean_ctor_get(v_m_2775_, 0);
    v___x_2777_ = lean_unsigned_to_nat(0);
    v___x_2778_ = lean_nat_dec_eq(v_size_2776_, v___x_2777_);
    return v___x_2778_;
}
pub unsafe fn l_Std_ExtDHashMap_isEmpty___boxed(
    mut v_00_u03b1_2779_: *mut LeanObject,
    mut v_00_u03b2_2780_: *mut LeanObject,
    mut v_x_2781_: *mut LeanObject,
    mut v_x_2782_: *mut LeanObject,
    mut v_inst_2783_: *mut LeanObject,
    mut v_inst_2784_: *mut LeanObject,
    mut v_m_2785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2786_: u8 = 0;
    let mut v_r_2787_: *mut LeanObject = core::ptr::null_mut();
    v_res_2786_ = l_Std_ExtDHashMap_isEmpty(
        v_00_u03b1_2779_,
        v_00_u03b2_2780_,
        v_x_2781_,
        v_x_2782_,
        v_inst_2783_,
        v_inst_2784_,
        v_m_2785_,
    );
    lean_dec(v_m_2785_);
    lean_dec_ref(v_x_2782_);
    lean_dec_ref(v_x_2781_);
    v_r_2787_ = lean_box((v_res_2786_) as usize);
    return v_r_2787_;
}
pub unsafe fn l_Std_ExtDHashMap_filter___redArg(
    mut v_f_2788_: *mut LeanObject,
    mut v_m_2789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    v___x_2790_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2788_, v_m_2789_);
    return v___x_2790_;
}
pub unsafe fn l_Std_ExtDHashMap_filter(
    mut v_00_u03b1_2791_: *mut LeanObject,
    mut v_00_u03b2_2792_: *mut LeanObject,
    mut v_x_2793_: *mut LeanObject,
    mut v_x_2794_: *mut LeanObject,
    mut v_inst_2795_: *mut LeanObject,
    mut v_inst_2796_: *mut LeanObject,
    mut v_f_2797_: *mut LeanObject,
    mut v_m_2798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    v___x_2799_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2797_, v_m_2798_);
    return v___x_2799_;
}
pub unsafe fn l_Std_ExtDHashMap_filter___boxed(
    mut v_00_u03b1_2800_: *mut LeanObject,
    mut v_00_u03b2_2801_: *mut LeanObject,
    mut v_x_2802_: *mut LeanObject,
    mut v_x_2803_: *mut LeanObject,
    mut v_inst_2804_: *mut LeanObject,
    mut v_inst_2805_: *mut LeanObject,
    mut v_f_2806_: *mut LeanObject,
    mut v_m_2807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2808_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_x_2803_);
    lean_dec_ref(v_x_2802_);
    return v_res_2808_;
}
pub unsafe fn l_Std_ExtDHashMap_map___redArg(
    mut v_f_2809_: *mut LeanObject,
    mut v_m_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    v___x_2811_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2809_, v_m_2810_);
    return v___x_2811_;
}
pub unsafe fn l_Std_ExtDHashMap_map(
    mut v_00_u03b1_2812_: *mut LeanObject,
    mut v_00_u03b2_2813_: *mut LeanObject,
    mut v_00_u03b3_2814_: *mut LeanObject,
    mut v_x_2815_: *mut LeanObject,
    mut v_x_2816_: *mut LeanObject,
    mut v_inst_2817_: *mut LeanObject,
    mut v_inst_2818_: *mut LeanObject,
    mut v_f_2819_: *mut LeanObject,
    mut v_m_2820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    v___x_2821_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2819_, v_m_2820_);
    return v___x_2821_;
}
pub unsafe fn l_Std_ExtDHashMap_map___boxed(
    mut v_00_u03b1_2822_: *mut LeanObject,
    mut v_00_u03b2_2823_: *mut LeanObject,
    mut v_00_u03b3_2824_: *mut LeanObject,
    mut v_x_2825_: *mut LeanObject,
    mut v_x_2826_: *mut LeanObject,
    mut v_inst_2827_: *mut LeanObject,
    mut v_inst_2828_: *mut LeanObject,
    mut v_f_2829_: *mut LeanObject,
    mut v_m_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2831_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_x_2826_);
    lean_dec_ref(v_x_2825_);
    return v_res_2831_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap___redArg(
    mut v_f_2832_: *mut LeanObject,
    mut v_m_2833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    v___x_2834_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2832_, v_m_2833_);
    return v___x_2834_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap(
    mut v_00_u03b1_2835_: *mut LeanObject,
    mut v_00_u03b2_2836_: *mut LeanObject,
    mut v_00_u03b3_2837_: *mut LeanObject,
    mut v_x_2838_: *mut LeanObject,
    mut v_x_2839_: *mut LeanObject,
    mut v_inst_2840_: *mut LeanObject,
    mut v_inst_2841_: *mut LeanObject,
    mut v_f_2842_: *mut LeanObject,
    mut v_m_2843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2842_, v_m_2843_);
    return v___x_2844_;
}
pub unsafe fn l_Std_ExtDHashMap_filterMap___boxed(
    mut v_00_u03b1_2845_: *mut LeanObject,
    mut v_00_u03b2_2846_: *mut LeanObject,
    mut v_00_u03b3_2847_: *mut LeanObject,
    mut v_x_2848_: *mut LeanObject,
    mut v_x_2849_: *mut LeanObject,
    mut v_inst_2850_: *mut LeanObject,
    mut v_inst_2851_: *mut LeanObject,
    mut v_f_2852_: *mut LeanObject,
    mut v_m_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2854_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_x_2849_);
    lean_dec_ref(v_x_2848_);
    return v_res_2854_;
}
pub unsafe fn l_Std_ExtDHashMap_modify___redArg(
    mut v_x_2855_: *mut LeanObject,
    mut v_x_2856_: *mut LeanObject,
    mut v_m_2857_: *mut LeanObject,
    mut v_a_2858_: *mut LeanObject,
    mut v_f_2859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_x_2855_, v_x_2856_, v_m_2857_, v_a_2858_, v_f_2859_,
    );
    return v___x_2860_;
}
pub unsafe fn l_Std_ExtDHashMap_modify(
    mut v_00_u03b1_2861_: *mut LeanObject,
    mut v_00_u03b2_2862_: *mut LeanObject,
    mut v_x_2863_: *mut LeanObject,
    mut v_x_2864_: *mut LeanObject,
    mut v_inst_2865_: *mut LeanObject,
    mut v_m_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
    mut v_f_2868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    v___x_2869_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_x_2863_, v_x_2864_, v_m_2866_, v_a_2867_, v_f_2868_,
    );
    return v___x_2869_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_modify___redArg(
    mut v_x_2870_: *mut LeanObject,
    mut v_x_2871_: *mut LeanObject,
    mut v_m_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_f_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    v___x_2875_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_2870_, v_x_2871_, v_m_2872_, v_a_2873_, v_f_2874_,
    );
    return v___x_2875_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_modify(
    mut v_00_u03b1_2876_: *mut LeanObject,
    mut v_x_2877_: *mut LeanObject,
    mut v_x_2878_: *mut LeanObject,
    mut v_inst_2879_: *mut LeanObject,
    mut v_inst_2880_: *mut LeanObject,
    mut v_00_u03b2_2881_: *mut LeanObject,
    mut v_m_2882_: *mut LeanObject,
    mut v_a_2883_: *mut LeanObject,
    mut v_f_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    v___x_2885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_2877_, v_x_2878_, v_m_2882_, v_a_2883_, v_f_2884_,
    );
    return v___x_2885_;
}
pub unsafe fn l_Std_ExtDHashMap_alter___redArg(
    mut v_x_2886_: *mut LeanObject,
    mut v_x_2887_: *mut LeanObject,
    mut v_m_2888_: *mut LeanObject,
    mut v_a_2889_: *mut LeanObject,
    mut v_f_2890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    v___x_2891_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_x_2886_, v_x_2887_, v_m_2888_, v_a_2889_, v_f_2890_,
    );
    return v___x_2891_;
}
pub unsafe fn l_Std_ExtDHashMap_alter(
    mut v_00_u03b1_2892_: *mut LeanObject,
    mut v_00_u03b2_2893_: *mut LeanObject,
    mut v_x_2894_: *mut LeanObject,
    mut v_x_2895_: *mut LeanObject,
    mut v_inst_2896_: *mut LeanObject,
    mut v_m_2897_: *mut LeanObject,
    mut v_a_2898_: *mut LeanObject,
    mut v_f_2899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    v___x_2900_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_x_2894_, v_x_2895_, v_m_2897_, v_a_2898_, v_f_2899_,
    );
    return v___x_2900_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_alter___redArg(
    mut v_x_2901_: *mut LeanObject,
    mut v_x_2902_: *mut LeanObject,
    mut v_m_2903_: *mut LeanObject,
    mut v_a_2904_: *mut LeanObject,
    mut v_f_2905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    v___x_2906_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_2901_, v_x_2902_, v_m_2903_, v_a_2904_, v_f_2905_,
    );
    return v___x_2906_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_alter(
    mut v_00_u03b1_2907_: *mut LeanObject,
    mut v_x_2908_: *mut LeanObject,
    mut v_x_2909_: *mut LeanObject,
    mut v_inst_2910_: *mut LeanObject,
    mut v_inst_2911_: *mut LeanObject,
    mut v_00_u03b2_2912_: *mut LeanObject,
    mut v_m_2913_: *mut LeanObject,
    mut v_a_2914_: *mut LeanObject,
    mut v_f_2915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    v___x_2916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_2908_, v_x_2909_, v_m_2913_, v_a_2914_, v_f_2915_,
    );
    return v___x_2916_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany___redArg___lam__0(
    mut v_x_2917_: *mut LeanObject,
    mut v_x_2918_: *mut LeanObject,
    mut v_x_2919_: *mut LeanObject,
    mut v_____s_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2921_ = lean_ctor_get(v_x_2919_, 0);
    lean_inc(v_fst_2921_);
    v_snd_2922_ = lean_ctor_get(v_x_2919_, 1);
    lean_inc(v_snd_2922_);
    lean_dec_ref(v_x_2919_);
    v_m_2923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2917_,
        v_x_2918_,
        v_____s_2920_,
        v_fst_2921_,
        v_snd_2922_,
    );
    v___x_2924_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2924_, 0, v_m_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany___redArg(
    mut v_x_2925_: *mut LeanObject,
    mut v_x_2926_: *mut LeanObject,
    mut v_inst_2927_: *mut LeanObject,
    mut v_m_2928_: *mut LeanObject,
    mut v_l_2929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    v___f_2930_ = lean_alloc_closure(
        l_Std_ExtDHashMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2930_, 0, v_x_2925_);
    lean_closure_set(v___f_2930_, 1, v_x_2926_);
    v___x_2931_ = lean_apply_4(v_inst_2927_, lean_box(0), v_l_2929_, v_m_2928_, v___f_2930_);
    return v___x_2931_;
}
pub unsafe fn l_Std_ExtDHashMap_insertMany(
    mut v_00_u03b1_2932_: *mut LeanObject,
    mut v_00_u03b2_2933_: *mut LeanObject,
    mut v_x_2934_: *mut LeanObject,
    mut v_x_2935_: *mut LeanObject,
    mut v_inst_2936_: *mut LeanObject,
    mut v_inst_2937_: *mut LeanObject,
    mut v_00_u03c1_2938_: *mut LeanObject,
    mut v_inst_2939_: *mut LeanObject,
    mut v_m_2940_: *mut LeanObject,
    mut v_l_2941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    v___f_2942_ = lean_alloc_closure(
        l_Std_ExtDHashMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2942_, 0, v_x_2934_);
    lean_closure_set(v___f_2942_, 1, v_x_2935_);
    v___x_2943_ = lean_apply_4(v_inst_2939_, lean_box(0), v_l_2941_, v_m_2940_, v___f_2942_);
    return v___x_2943_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0(
    mut v_x_2944_: *mut LeanObject,
    mut v_x_2945_: *mut LeanObject,
    mut v_x_2946_: *mut LeanObject,
    mut v_____s_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2948_ = lean_ctor_get(v_x_2946_, 0);
    lean_inc(v_fst_2948_);
    v_snd_2949_ = lean_ctor_get(v_x_2946_, 1);
    lean_inc(v_snd_2949_);
    lean_dec_ref(v_x_2946_);
    v_m_2950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2944_,
        v_x_2945_,
        v_____s_2947_,
        v_fst_2948_,
        v_snd_2949_,
    );
    v___x_2951_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2951_, 0, v_m_2950_);
    return v___x_2951_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany___redArg(
    mut v_x_2952_: *mut LeanObject,
    mut v_x_2953_: *mut LeanObject,
    mut v_inst_2954_: *mut LeanObject,
    mut v_m_2955_: *mut LeanObject,
    mut v_l_2956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    v___f_2957_ = lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2957_, 0, v_x_2952_);
    lean_closure_set(v___f_2957_, 1, v_x_2953_);
    v___x_2958_ = lean_apply_4(v_inst_2954_, lean_box(0), v_l_2956_, v_m_2955_, v___f_2957_);
    return v___x_2958_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertMany(
    mut v_00_u03b1_2959_: *mut LeanObject,
    mut v_x_2960_: *mut LeanObject,
    mut v_x_2961_: *mut LeanObject,
    mut v_inst_2962_: *mut LeanObject,
    mut v_inst_2963_: *mut LeanObject,
    mut v_00_u03b2_2964_: *mut LeanObject,
    mut v_00_u03c1_2965_: *mut LeanObject,
    mut v_inst_2966_: *mut LeanObject,
    mut v_m_2967_: *mut LeanObject,
    mut v_l_2968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    v___f_2969_ = lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2969_, 0, v_x_2960_);
    lean_closure_set(v___f_2969_, 1, v_x_2961_);
    v___x_2970_ = lean_apply_4(v_inst_2966_, lean_box(0), v_l_2968_, v_m_2967_, v___f_2969_);
    return v___x_2970_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0(
    mut v_x_2971_: *mut LeanObject,
    mut v_x_2972_: *mut LeanObject,
    mut v_a_2973_: *mut LeanObject,
    mut v_____s_2974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    v___x_2975_ = lean_box(0);
    v_m_2976_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2971_,
        v_x_2972_,
        v_____s_2974_,
        v_a_2973_,
        v___x_2975_,
    );
    v___x_2977_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2977_, 0, v_m_2976_);
    return v___x_2977_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg(
    mut v_x_2978_: *mut LeanObject,
    mut v_x_2979_: *mut LeanObject,
    mut v_inst_2980_: *mut LeanObject,
    mut v_m_2981_: *mut LeanObject,
    mut v_l_2982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    v___f_2983_ = lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2983_, 0, v_x_2978_);
    lean_closure_set(v___f_2983_, 1, v_x_2979_);
    v___x_2984_ = lean_apply_4(v_inst_2980_, lean_box(0), v_l_2982_, v_m_2981_, v___f_2983_);
    return v___x_2984_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_insertManyIfNewUnit(
    mut v_00_u03b1_2985_: *mut LeanObject,
    mut v_x_2986_: *mut LeanObject,
    mut v_x_2987_: *mut LeanObject,
    mut v_inst_2988_: *mut LeanObject,
    mut v_inst_2989_: *mut LeanObject,
    mut v_00_u03c1_2990_: *mut LeanObject,
    mut v_inst_2991_: *mut LeanObject,
    mut v_m_2992_: *mut LeanObject,
    mut v_l_2993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    v___f_2994_ = lean_alloc_closure(
        l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2994_, 0, v_x_2986_);
    lean_closure_set(v___f_2994_, 1, v_x_2987_);
    v___x_2995_ = lean_apply_4(v_inst_2991_, lean_box(0), v_l_2993_, v_m_2992_, v___f_2994_);
    return v___x_2995_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg___lam__0(
    mut v_x_2996_: *mut LeanObject,
    mut v_x_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
    mut v_b_2999_: *mut LeanObject,
    mut v_acc_3000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    v_r_3001_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2996_,
        v_x_2997_,
        v_acc_3000_,
        v_a_2998_,
        v_b_2999_,
    );
    v___x_3002_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3002_, 0, v_r_3001_);
    return v___x_3002_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg___lam__1(
    mut v___x_3003_: *mut LeanObject,
    mut v___f_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
    mut v_x_3006_: *mut LeanObject,
    mut v___y_3007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    v___x_3008_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_3003_, v___f_3004_, v_a_3005_, v___y_3007_);
    return v___x_3008_;
}
pub unsafe fn l_Std_ExtDHashMap_union___redArg(
    mut v_x_3030_: *mut LeanObject,
    mut v_x_3031_: *mut LeanObject,
    mut v_m_u2081_3032_: *mut LeanObject,
    mut v_m_u2082_3033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: u8 = 0;
    v_size_3034_ = lean_ctor_get(v_m_u2081_3032_, 0);
    v_buckets_3035_ = lean_ctor_get(v_m_u2081_3032_, 1);
    v_size_3036_ = lean_ctor_get(v_m_u2082_3033_, 0);
    v___x_3037_ = lean_nat_dec_le(v_size_3034_, v_size_3036_);
    if v___x_3037_ == 0 {
        let mut v___f_3038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___f_3040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3042_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3043_: usize = 0;
        let mut v___x_3044_: usize = 0;
        let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_buckets_3035_);
        lean_dec(v_m_u2081_3032_);
        v___f_3040_ = lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        lean_closure_set(v___f_3040_, 0, v_x_3030_);
        lean_closure_set(v___f_3040_, 1, v_x_3031_);
        v___x_3041_ = l_Std_ExtDHashMap_union___redArg___closed__9;
        v___f_3042_ = lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        lean_closure_set(v___f_3042_, 0, v___x_3041_);
        lean_closure_set(v___f_3042_, 1, v___f_3040_);
        v_sz_3043_ = lean_array_size(v_buckets_3035_);
        v___x_3044_ = 0usize;
        v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b1_3046_: *mut LeanObject,
    mut v_00_u03b2_3047_: *mut LeanObject,
    mut v_x_3048_: *mut LeanObject,
    mut v_x_3049_: *mut LeanObject,
    mut v_inst_3050_: *mut LeanObject,
    mut v_inst_3051_: *mut LeanObject,
    mut v_m_u2081_3052_: *mut LeanObject,
    mut v_m_u2082_3053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    v_size_3054_ = lean_ctor_get(v_m_u2081_3052_, 0);
    v_buckets_3055_ = lean_ctor_get(v_m_u2081_3052_, 1);
    v_size_3056_ = lean_ctor_get(v_m_u2082_3053_, 0);
    v___x_3057_ = lean_nat_dec_le(v_size_3054_, v_size_3056_);
    if v___x_3057_ == 0 {
        let mut v___f_3058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___f_3060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3062_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3063_: usize = 0;
        let mut v___x_3064_: usize = 0;
        let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_buckets_3055_);
        lean_dec(v_m_u2081_3052_);
        v___f_3060_ = lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        lean_closure_set(v___f_3060_, 0, v_x_3048_);
        lean_closure_set(v___f_3060_, 1, v_x_3049_);
        v___x_3061_ = l_Std_ExtDHashMap_union___redArg___closed__9;
        v___f_3062_ = lean_alloc_closure(
            l_Std_ExtDHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        lean_closure_set(v___f_3062_, 0, v___x_3061_);
        lean_closure_set(v___f_3062_, 1, v___f_3060_);
        v_sz_3063_ = lean_array_size(v_buckets_3055_);
        v___x_3064_ = 0usize;
        v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_x_3066_: *mut LeanObject,
    mut v_x_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    v___x_3068_ = lean_alloc_closure(l_Std_ExtDHashMap_union as *mut core::ffi::c_void, 8, 6);
    lean_closure_set(v___x_3068_, 0, lean_box(0));
    lean_closure_set(v___x_3068_, 1, lean_box(0));
    lean_closure_set(v___x_3068_, 2, v_x_3066_);
    lean_closure_set(v___x_3068_, 3, v_x_3067_);
    lean_closure_set(v___x_3068_, 4, lean_box(0));
    lean_closure_set(v___x_3068_, 5, lean_box(0));
    return v___x_3068_;
}
pub unsafe fn l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3069_: *mut LeanObject,
    mut v_00_u03b2_3070_: *mut LeanObject,
    mut v_x_3071_: *mut LeanObject,
    mut v_x_3072_: *mut LeanObject,
    mut v_inst_3073_: *mut LeanObject,
    mut v_inst_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    v___x_3075_ = lean_alloc_closure(l_Std_ExtDHashMap_union as *mut core::ffi::c_void, 8, 6);
    lean_closure_set(v___x_3075_, 0, lean_box(0));
    lean_closure_set(v___x_3075_, 1, lean_box(0));
    lean_closure_set(v___x_3075_, 2, v_x_3071_);
    lean_closure_set(v___x_3075_, 3, v_x_3072_);
    lean_closure_set(v___x_3075_, 4, lean_box(0));
    lean_closure_set(v___x_3075_, 5, lean_box(0));
    return v___x_3075_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(
    mut v_x_3076_: *mut LeanObject,
    mut v_x_3077_: *mut LeanObject,
    mut v_inst_3078_: *mut LeanObject,
    mut v_m_u2081_3079_: *mut LeanObject,
    mut v_m_u2082_3080_: *mut LeanObject,
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
    mut v_x_3082_: *mut LeanObject,
    mut v_x_3083_: *mut LeanObject,
    mut v_inst_3084_: *mut LeanObject,
    mut v_m_u2081_3085_: *mut LeanObject,
    mut v_m_u2082_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3087_: u8 = 0;
    let mut v_r_3088_: *mut LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(
        v_x_3082_,
        v_x_3083_,
        v_inst_3084_,
        v_m_u2081_3085_,
        v_m_u2082_3086_,
    );
    v_r_3088_ = lean_box((v_res_3087_) as usize);
    return v_r_3088_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg(
    mut v_x_3089_: *mut LeanObject,
    mut v_x_3090_: *mut LeanObject,
    mut v_inst_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3092_: *mut LeanObject = core::ptr::null_mut();
    v___f_3092_ = lean_alloc_closure(
        l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_3092_, 0, v_x_3089_);
    lean_closure_set(v___f_3092_, 1, v_x_3090_);
    lean_closure_set(v___f_3092_, 2, v_inst_3091_);
    return v___f_3092_;
}
pub unsafe fn l_Std_ExtDHashMap_instBEqOfLawfulBEq(
    mut v_00_u03b1_3093_: *mut LeanObject,
    mut v_00_u03b2_3094_: *mut LeanObject,
    mut v_x_3095_: *mut LeanObject,
    mut v_x_3096_: *mut LeanObject,
    mut v_inst_3097_: *mut LeanObject,
    mut v_inst_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3099_: *mut LeanObject = core::ptr::null_mut();
    v___f_3099_ = lean_alloc_closure(
        l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_3099_, 0, v_x_3095_);
    lean_closure_set(v___f_3099_, 1, v_x_3096_);
    lean_closure_set(v___f_3099_, 2, v_inst_3098_);
    return v___f_3099_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(
    mut v_inst_3100_: *mut LeanObject,
    mut v_inst_3101_: *mut LeanObject,
    mut v_inst_3102_: *mut LeanObject,
    mut v_x_3103_: *mut LeanObject,
    mut v_x_3104_: *mut LeanObject,
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
    mut v_inst_3106_: *mut LeanObject,
    mut v_inst_3107_: *mut LeanObject,
    mut v_inst_3108_: *mut LeanObject,
    mut v_x_3109_: *mut LeanObject,
    mut v_x_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3111_: u8 = 0;
    let mut v_r_3112_: *mut LeanObject = core::ptr::null_mut();
    v_res_3111_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(
        v_inst_3106_,
        v_inst_3107_,
        v_inst_3108_,
        v_x_3109_,
        v_x_3110_,
    );
    v_r_3112_ = lean_box((v_res_3111_) as usize);
    return v_r_3112_;
}
pub unsafe fn l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(
    mut v_00_u03b1_3113_: *mut LeanObject,
    mut v_00_u03b2_3114_: *mut LeanObject,
    mut v_inst_3115_: *mut LeanObject,
    mut v_inst_3116_: *mut LeanObject,
    mut v_inst_3117_: *mut LeanObject,
    mut v_inst_3118_: *mut LeanObject,
    mut v_inst_3119_: *mut LeanObject,
    mut v_x_3120_: *mut LeanObject,
    mut v_x_3121_: *mut LeanObject,
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
    mut v_00_u03b1_3123_: *mut LeanObject,
    mut v_00_u03b2_3124_: *mut LeanObject,
    mut v_inst_3125_: *mut LeanObject,
    mut v_inst_3126_: *mut LeanObject,
    mut v_inst_3127_: *mut LeanObject,
    mut v_inst_3128_: *mut LeanObject,
    mut v_inst_3129_: *mut LeanObject,
    mut v_x_3130_: *mut LeanObject,
    mut v_x_3131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3132_: u8 = 0;
    let mut v_r_3133_: *mut LeanObject = core::ptr::null_mut();
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
    v_r_3133_ = lean_box((v_res_3132_) as usize);
    return v_r_3133_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_beq___redArg(
    mut v_x_3134_: *mut LeanObject,
    mut v_x_3135_: *mut LeanObject,
    mut v_inst_3136_: *mut LeanObject,
    mut v_m_u2081_3137_: *mut LeanObject,
    mut v_m_u2082_3138_: *mut LeanObject,
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
    mut v_x_3140_: *mut LeanObject,
    mut v_x_3141_: *mut LeanObject,
    mut v_inst_3142_: *mut LeanObject,
    mut v_m_u2081_3143_: *mut LeanObject,
    mut v_m_u2082_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3145_: u8 = 0;
    let mut v_r_3146_: *mut LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Std_ExtDHashMap_Const_beq___redArg(
        v_x_3140_,
        v_x_3141_,
        v_inst_3142_,
        v_m_u2081_3143_,
        v_m_u2082_3144_,
    );
    v_r_3146_ = lean_box((v_res_3145_) as usize);
    return v_r_3146_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_beq(
    mut v_00_u03b1_3147_: *mut LeanObject,
    mut v_x_3148_: *mut LeanObject,
    mut v_x_3149_: *mut LeanObject,
    mut v_00_u03b2_3150_: *mut LeanObject,
    mut v_inst_3151_: *mut LeanObject,
    mut v_inst_3152_: *mut LeanObject,
    mut v_inst_3153_: *mut LeanObject,
    mut v_m_u2081_3154_: *mut LeanObject,
    mut v_m_u2082_3155_: *mut LeanObject,
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
    mut v_00_u03b1_3157_: *mut LeanObject,
    mut v_x_3158_: *mut LeanObject,
    mut v_x_3159_: *mut LeanObject,
    mut v_00_u03b2_3160_: *mut LeanObject,
    mut v_inst_3161_: *mut LeanObject,
    mut v_inst_3162_: *mut LeanObject,
    mut v_inst_3163_: *mut LeanObject,
    mut v_m_u2081_3164_: *mut LeanObject,
    mut v_m_u2082_3165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3166_: u8 = 0;
    let mut v_r_3167_: *mut LeanObject = core::ptr::null_mut();
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
    v_r_3167_ = lean_box((v_res_3166_) as usize);
    return v_r_3167_;
}
pub unsafe fn l_Std_ExtDHashMap_inter___redArg(
    mut v_x_3168_: *mut LeanObject,
    mut v_x_3169_: *mut LeanObject,
    mut v_m_u2081_3170_: *mut LeanObject,
    mut v_m_u2082_3171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    v___x_3172_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_3168_,
        v_x_3169_,
        v_m_u2081_3170_,
        v_m_u2082_3171_,
    );
    return v___x_3172_;
}
pub unsafe fn l_Std_ExtDHashMap_inter(
    mut v_00_u03b1_3173_: *mut LeanObject,
    mut v_00_u03b2_3174_: *mut LeanObject,
    mut v_x_3175_: *mut LeanObject,
    mut v_x_3176_: *mut LeanObject,
    mut v_inst_3177_: *mut LeanObject,
    mut v_inst_3178_: *mut LeanObject,
    mut v_m_u2081_3179_: *mut LeanObject,
    mut v_m_u2082_3180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    v___x_3181_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_3175_,
        v_x_3176_,
        v_m_u2081_3179_,
        v_m_u2082_3180_,
    );
    return v___x_3181_;
}
pub unsafe fn l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_3182_: *mut LeanObject,
    mut v_x_3183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    v___x_3184_ = lean_alloc_closure(l_Std_ExtDHashMap_inter as *mut core::ffi::c_void, 8, 6);
    lean_closure_set(v___x_3184_, 0, lean_box(0));
    lean_closure_set(v___x_3184_, 1, lean_box(0));
    lean_closure_set(v___x_3184_, 2, v_x_3182_);
    lean_closure_set(v___x_3184_, 3, v_x_3183_);
    lean_closure_set(v___x_3184_, 4, lean_box(0));
    lean_closure_set(v___x_3184_, 5, lean_box(0));
    return v___x_3184_;
}
pub unsafe fn l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3185_: *mut LeanObject,
    mut v_00_u03b2_3186_: *mut LeanObject,
    mut v_x_3187_: *mut LeanObject,
    mut v_x_3188_: *mut LeanObject,
    mut v_inst_3189_: *mut LeanObject,
    mut v_inst_3190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    v___x_3191_ = lean_alloc_closure(l_Std_ExtDHashMap_inter as *mut core::ffi::c_void, 8, 6);
    lean_closure_set(v___x_3191_, 0, lean_box(0));
    lean_closure_set(v___x_3191_, 1, lean_box(0));
    lean_closure_set(v___x_3191_, 2, v_x_3187_);
    lean_closure_set(v___x_3191_, 3, v_x_3188_);
    lean_closure_set(v___x_3191_, 4, lean_box(0));
    lean_closure_set(v___x_3191_, 5, lean_box(0));
    return v___x_3191_;
}
pub unsafe fn l_Std_ExtDHashMap_diff___redArg___lam__0(
    mut v_x_3192_: *mut LeanObject,
    mut v_x_3193_: *mut LeanObject,
    mut v_m_u2082_3194_: *mut LeanObject,
    mut v___x_3195_: u8,
    mut v_k_3196_: *mut LeanObject,
    mut v_x_3197_: *mut LeanObject,
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
    mut v_x_3200_: *mut LeanObject,
    mut v_x_3201_: *mut LeanObject,
    mut v_m_u2082_3202_: *mut LeanObject,
    mut v___x_3203_: *mut LeanObject,
    mut v_k_3204_: *mut LeanObject,
    mut v_x_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_108__boxed_3206_: u8 = 0;
    let mut v_res_3207_: u8 = 0;
    let mut v_r_3208_: *mut LeanObject = core::ptr::null_mut();
    v___x_108__boxed_3206_ = (lean_unbox(v___x_3203_) as u8);
    v_res_3207_ = l_Std_ExtDHashMap_diff___redArg___lam__0(
        v_x_3200_,
        v_x_3201_,
        v_m_u2082_3202_,
        v___x_108__boxed_3206_,
        v_k_3204_,
        v_x_3205_,
    );
    lean_dec(v_x_3205_);
    lean_dec(v_m_u2082_3202_);
    v_r_3208_ = lean_box((v_res_3207_) as usize);
    return v_r_3208_;
}
pub unsafe fn l_Std_ExtDHashMap_diff___redArg(
    mut v_x_3209_: *mut LeanObject,
    mut v_x_3210_: *mut LeanObject,
    mut v_m_u2081_3211_: *mut LeanObject,
    mut v_m_u2082_3212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    v_size_3213_ = lean_ctor_get(v_m_u2081_3211_, 0);
    v_size_3214_ = lean_ctor_get(v_m_u2082_3212_, 0);
    v___x_3215_ = lean_nat_dec_le(v_size_3213_, v_size_3214_);
    if v___x_3215_ == 0 {
        let mut v___f_3216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
        v___x_3218_ = lean_box((v___x_3215_) as usize);
        v___f_3219_ = lean_alloc_closure(
            l_Std_ExtDHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        lean_closure_set(v___f_3219_, 0, v_x_3209_);
        lean_closure_set(v___f_3219_, 1, v_x_3210_);
        lean_closure_set(v___f_3219_, 2, v_m_u2082_3212_);
        lean_closure_set(v___f_3219_, 3, v___x_3218_);
        v___x_3220_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3219_, v_m_u2081_3211_);
        return v___x_3220_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_diff(
    mut v_00_u03b1_3221_: *mut LeanObject,
    mut v_00_u03b2_3222_: *mut LeanObject,
    mut v_x_3223_: *mut LeanObject,
    mut v_x_3224_: *mut LeanObject,
    mut v_inst_3225_: *mut LeanObject,
    mut v_inst_3226_: *mut LeanObject,
    mut v_m_u2081_3227_: *mut LeanObject,
    mut v_m_u2082_3228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    v_size_3229_ = lean_ctor_get(v_m_u2081_3227_, 0);
    v_size_3230_ = lean_ctor_get(v_m_u2082_3228_, 0);
    v___x_3231_ = lean_nat_dec_le(v_size_3229_, v_size_3230_);
    if v___x_3231_ == 0 {
        let mut v___f_3232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
        v___x_3234_ = lean_box((v___x_3231_) as usize);
        v___f_3235_ = lean_alloc_closure(
            l_Std_ExtDHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        lean_closure_set(v___f_3235_, 0, v_x_3223_);
        lean_closure_set(v___f_3235_, 1, v_x_3224_);
        lean_closure_set(v___f_3235_, 2, v_m_u2082_3228_);
        lean_closure_set(v___f_3235_, 3, v___x_3234_);
        v___x_3236_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3235_, v_m_u2081_3227_);
        return v___x_3236_;
    }
}
pub unsafe fn l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_3237_: *mut LeanObject,
    mut v_x_3238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    v___x_3239_ = lean_alloc_closure(l_Std_ExtDHashMap_diff as *mut core::ffi::c_void, 8, 6);
    lean_closure_set(v___x_3239_, 0, lean_box(0));
    lean_closure_set(v___x_3239_, 1, lean_box(0));
    lean_closure_set(v___x_3239_, 2, v_x_3237_);
    lean_closure_set(v___x_3239_, 3, v_x_3238_);
    lean_closure_set(v___x_3239_, 4, lean_box(0));
    lean_closure_set(v___x_3239_, 5, lean_box(0));
    return v___x_3239_;
}
pub unsafe fn l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_3240_: *mut LeanObject,
    mut v_00_u03b2_3241_: *mut LeanObject,
    mut v_x_3242_: *mut LeanObject,
    mut v_x_3243_: *mut LeanObject,
    mut v_inst_3244_: *mut LeanObject,
    mut v_inst_3245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    v___x_3246_ = lean_alloc_closure(l_Std_ExtDHashMap_diff as *mut core::ffi::c_void, 8, 6);
    lean_closure_set(v___x_3246_, 0, lean_box(0));
    lean_closure_set(v___x_3246_, 1, lean_box(0));
    lean_closure_set(v___x_3246_, 2, v_x_3242_);
    lean_closure_set(v___x_3246_, 3, v_x_3243_);
    lean_closure_set(v___x_3246_, 4, lean_box(0));
    lean_closure_set(v___x_3246_, 5, lean_box(0));
    return v___x_3246_;
}
pub unsafe fn l_Std_ExtDHashMap_Const_unitOfArray___redArg(
    mut v_inst_3251_: *mut LeanObject,
    mut v_inst_3252_: *mut LeanObject,
    mut v_l_3253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    v___f_3254_ = l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_3255_ = lean_obj_once(
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
    mut v_00_u03b1_3257_: *mut LeanObject,
    mut v_inst_3258_: *mut LeanObject,
    mut v_inst_3259_: *mut LeanObject,
    mut v_l_3260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    v___f_3261_ = l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_3262_ = lean_obj_once(
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
    mut v_inst_3268_: *mut LeanObject,
    mut v_inst_3269_: *mut LeanObject,
    mut v_l_3270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    v___f_3271_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3272_ = lean_obj_once(
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
    mut v_00_u03b1_3274_: *mut LeanObject,
    mut v_00_u03b2_3275_: *mut LeanObject,
    mut v_inst_3276_: *mut LeanObject,
    mut v_inst_3277_: *mut LeanObject,
    mut v_l_3278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    v___f_3279_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3280_ = lean_obj_once(
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
    mut v_inst_3282_: *mut LeanObject,
    mut v_inst_3283_: *mut LeanObject,
    mut v_l_3284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    v___f_3285_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3286_ = lean_obj_once(
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
    mut v_00_u03b1_3288_: *mut LeanObject,
    mut v_00_u03b2_3289_: *mut LeanObject,
    mut v_inst_3290_: *mut LeanObject,
    mut v_inst_3291_: *mut LeanObject,
    mut v_l_3292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    v___f_3293_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3294_ = lean_obj_once(
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
    mut v_inst_3296_: *mut LeanObject,
    mut v_inst_3297_: *mut LeanObject,
    mut v_l_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    v___f_3299_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3300_ = lean_obj_once(
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
    mut v_00_u03b1_3302_: *mut LeanObject,
    mut v_inst_3303_: *mut LeanObject,
    mut v_inst_3304_: *mut LeanObject,
    mut v_l_3305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    v___f_3306_ = l_Std_ExtDHashMap_ofList___redArg___closed__1;
    v___x_3307_ = lean_obj_once(
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
pub unsafe fn runtime_initialize_Std_Data_ExtDHashMap_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtDHashMap_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_ExtDHashMap_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtDHashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtDHashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_ExtDHashMap_Basic(builtin);
}
