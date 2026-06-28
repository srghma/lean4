// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Model
// Imports: Std.Data.DTreeMap.Internal.WF.Defs Std.Data.DTreeMap.Internal.Cell Init.Data.Nat.Linear Init.Omega
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_head_x3f___redArg};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DTreeMap::Internal::Cell::{
    initialize_Std_Data_DTreeMap_Internal_Cell,
    l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg,
    l_Std_DTreeMap_Internal_Cell_contains___redArg, l_Std_DTreeMap_Internal_Cell_get_x3f___redArg,
    l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg,
    l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg, l_Std_DTreeMap_Internal_Cell_ofEq___redArg,
    runtime_initialize_Std_Data_DTreeMap_Internal_Cell,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Def::l_Std_DTreeMap_Internal_Impl_toListModel___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::WF::Defs::{
    initialize_Std_Data_DTreeMap_Internal_WF_Defs,
    runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs,
};
pub static l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(
    mut v_k_3131_: *mut crate::leanh::LeanObject,
    mut v_l_3132_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_3132_) == 0 {
                    v_k_3133_ = crate::leanh::lean_ctor_get(v_l_3132_, 1);
                    crate::leanh::lean_inc(v_k_3133_);
                    v_l_3134_ = crate::leanh::lean_ctor_get(v_l_3132_, 3);
                    crate::leanh::lean_inc(v_l_3134_);
                    v_r_3135_ = crate::leanh::lean_ctor_get(v_l_3132_, 4);
                    crate::leanh::lean_inc(v_r_3135_);
                    crate::leanh::lean_dec_ref_known(v_l_3132_, 5);
                    crate::leanh::lean_inc_ref(v_k_3131_);
                    v___x_3136_ = crate::leanh::lean_apply_1(v_k_3131_, v_k_3133_);
                    v___x_3137_ = (crate::leanh::lean_unbox(v___x_3136_) as u8);
                    match v___x_3137_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_3135_);
                            v_l_3132_ = v_l_3134_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_3135_);
                            crate::leanh::lean_dec(v_l_3134_);
                            crate::leanh::lean_dec_ref(v_k_3131_);
                            v___x_3139_ = 1;
                            return v___x_3139_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_3134_);
                            v_l_3132_ = v_r_3135_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_3131_);
                    v___x_3141_ = 0;
                    return v___x_3141_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_x27___redArg___boxed(
    mut v_k_3142_: *mut crate::leanh::LeanObject,
    mut v_l_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3144_: u8 = 0;
    let mut v_r_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3144_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_3142_, v_l_3143_);
    v_r_3145_ = crate::leanh::lean_box((v_res_3144_) as usize);
    return v_r_3145_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_x27(
    mut v_00_u03b1_3146_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3147_: *mut crate::leanh::LeanObject,
    mut v_inst_3148_: *mut crate::leanh::LeanObject,
    mut v_k_3149_: *mut crate::leanh::LeanObject,
    mut v_l_3150_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3151_: u8 = 0;
    v___x_3151_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_3149_, v_l_3150_);
    return v___x_3151_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_x27___boxed(
    mut v_00_u03b1_3152_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3153_: *mut crate::leanh::LeanObject,
    mut v_inst_3154_: *mut crate::leanh::LeanObject,
    mut v_k_3155_: *mut crate::leanh::LeanObject,
    mut v_l_3156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3157_: u8 = 0;
    let mut v_r_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3157_ = l_Std_DTreeMap_Internal_Impl_contains_x27(
        v_00_u03b1_3152_,
        v_00_u03b2_3153_,
        v_inst_3154_,
        v_k_3155_,
        v_l_3156_,
    );
    crate::leanh::lean_dec_ref(v_inst_3154_);
    v_r_3158_ = crate::leanh::lean_box((v_res_3157_) as usize);
    return v_r_3158_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(
    mut v_l_3159_: *mut crate::leanh::LeanObject,
    mut v_h__1_3160_: *mut crate::leanh::LeanObject,
    mut v_h__2_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3159_) == 0 {
        let mut v_size_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3160_);
        v_size_3162_ = crate::leanh::lean_ctor_get(v_l_3159_, 0);
        crate::leanh::lean_inc(v_size_3162_);
        v_k_3163_ = crate::leanh::lean_ctor_get(v_l_3159_, 1);
        crate::leanh::lean_inc(v_k_3163_);
        v_v_3164_ = crate::leanh::lean_ctor_get(v_l_3159_, 2);
        crate::leanh::lean_inc(v_v_3164_);
        v_l_3165_ = crate::leanh::lean_ctor_get(v_l_3159_, 3);
        crate::leanh::lean_inc(v_l_3165_);
        v_r_3166_ = crate::leanh::lean_ctor_get(v_l_3159_, 4);
        crate::leanh::lean_inc(v_r_3166_);
        crate::leanh::lean_dec_ref_known(v_l_3159_, 5);
        v___x_3167_ = crate::leanh::lean_apply_5(
            v_h__2_3161_,
            v_size_3162_,
            v_k_3163_,
            v_v_3164_,
            v_l_3165_,
            v_r_3166_,
        );
        return v___x_3167_;
    } else {
        let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3161_);
        v___x_3168_ = crate::leanh::lean_box(0);
        v___x_3169_ = crate::leanh::lean_apply_1(v_h__1_3160_, v___x_3168_);
        return v___x_3169_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(
    mut v_00_u03b1_3170_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3171_: *mut crate::leanh::LeanObject,
    mut v_motive_3172_: *mut crate::leanh::LeanObject,
    mut v_l_3173_: *mut crate::leanh::LeanObject,
    mut v_h__1_3174_: *mut crate::leanh::LeanObject,
    mut v_h__2_3175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3173_) == 0 {
        let mut v_size_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3174_);
        v_size_3176_ = crate::leanh::lean_ctor_get(v_l_3173_, 0);
        crate::leanh::lean_inc(v_size_3176_);
        v_k_3177_ = crate::leanh::lean_ctor_get(v_l_3173_, 1);
        crate::leanh::lean_inc(v_k_3177_);
        v_v_3178_ = crate::leanh::lean_ctor_get(v_l_3173_, 2);
        crate::leanh::lean_inc(v_v_3178_);
        v_l_3179_ = crate::leanh::lean_ctor_get(v_l_3173_, 3);
        crate::leanh::lean_inc(v_l_3179_);
        v_r_3180_ = crate::leanh::lean_ctor_get(v_l_3173_, 4);
        crate::leanh::lean_inc(v_r_3180_);
        crate::leanh::lean_dec_ref_known(v_l_3173_, 5);
        v___x_3181_ = crate::leanh::lean_apply_5(
            v_h__2_3175_,
            v_size_3176_,
            v_k_3177_,
            v_v_3178_,
            v_l_3179_,
            v_r_3180_,
        );
        return v___x_3181_;
    } else {
        let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3175_);
        v___x_3182_ = crate::leanh::lean_box(0);
        v___x_3183_ = crate::leanh::lean_apply_1(v_h__1_3174_, v___x_3182_);
        return v___x_3183_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(
    mut v_x_3184_: u8,
    mut v_h__1_3185_: *mut crate::leanh::LeanObject,
    mut v_h__2_3186_: *mut crate::leanh::LeanObject,
    mut v_h__3_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_3184_ {
        0 => {
            let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3187_);
            crate::leanh::lean_dec(v_h__2_3186_);
            v___x_3188_ = crate::leanh::lean_box(0);
            v___x_3189_ = crate::leanh::lean_apply_1(v_h__1_3185_, v___x_3188_);
            return v___x_3189_;
        }
        1 => {
            let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3186_);
            crate::leanh::lean_dec(v_h__1_3185_);
            v___x_3190_ = crate::leanh::lean_box(0);
            v___x_3191_ = crate::leanh::lean_apply_1(v_h__3_3187_, v___x_3190_);
            return v___x_3191_;
        }
        _ => {
            let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3187_);
            crate::leanh::lean_dec(v_h__1_3185_);
            v___x_3192_ = crate::leanh::lean_box(0);
            v___x_3193_ = crate::leanh::lean_apply_1(v_h__2_3186_, v___x_3192_);
            return v___x_3193_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(
    mut v_x_3194_: *mut crate::leanh::LeanObject,
    mut v_h__1_3195_: *mut crate::leanh::LeanObject,
    mut v_h__2_3196_: *mut crate::leanh::LeanObject,
    mut v_h__3_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_3198_: u8 = 0;
    let mut v_res_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_3198_ = (crate::leanh::lean_unbox(v_x_3194_) as u8);
    v_res_3199_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_36__boxed_3198_, v_h__1_3195_, v_h__2_3196_, v_h__3_3197_);
    return v_res_3199_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(
    mut v_motive_3200_: *mut crate::leanh::LeanObject,
    mut v_x_3201_: u8,
    mut v_h__1_3202_: *mut crate::leanh::LeanObject,
    mut v_h__2_3203_: *mut crate::leanh::LeanObject,
    mut v_h__3_3204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_3201_ {
        0 => {
            let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3204_);
            crate::leanh::lean_dec(v_h__2_3203_);
            v___x_3205_ = crate::leanh::lean_box(0);
            v___x_3206_ = crate::leanh::lean_apply_1(v_h__1_3202_, v___x_3205_);
            return v___x_3206_;
        }
        1 => {
            let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3203_);
            crate::leanh::lean_dec(v_h__1_3202_);
            v___x_3207_ = crate::leanh::lean_box(0);
            v___x_3208_ = crate::leanh::lean_apply_1(v_h__3_3204_, v___x_3207_);
            return v___x_3208_;
        }
        _ => {
            let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3204_);
            crate::leanh::lean_dec(v_h__1_3202_);
            v___x_3209_ = crate::leanh::lean_box(0);
            v___x_3210_ = crate::leanh::lean_apply_1(v_h__2_3203_, v___x_3209_);
            return v___x_3210_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(
    mut v_motive_3211_: *mut crate::leanh::LeanObject,
    mut v_x_3212_: *mut crate::leanh::LeanObject,
    mut v_h__1_3213_: *mut crate::leanh::LeanObject,
    mut v_h__2_3214_: *mut crate::leanh::LeanObject,
    mut v_h__3_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_3216_: u8 = 0;
    let mut v_res_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_3216_ = (crate::leanh::lean_unbox(v_x_3212_) as u8);
    v_res_3217_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_3211_, v_x_51__boxed_3216_, v_h__1_3213_, v_h__2_3214_, v_h__3_3215_);
    return v_res_3217_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(
    mut v_x_3218_: u8,
    mut v_h__1_3219_: *mut crate::leanh::LeanObject,
    mut v_h__2_3220_: *mut crate::leanh::LeanObject,
    mut v_h__3_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_3218_ {
        0 => {
            let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3221_);
            crate::leanh::lean_dec(v_h__2_3220_);
            v___x_3222_ = crate::leanh::lean_box(0);
            v___x_3223_ = crate::leanh::lean_apply_1(v_h__1_3219_, v___x_3222_);
            return v___x_3223_;
        }
        1 => {
            let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3220_);
            crate::leanh::lean_dec(v_h__1_3219_);
            v___x_3224_ = crate::leanh::lean_box(0);
            v___x_3225_ = crate::leanh::lean_apply_1(v_h__3_3221_, v___x_3224_);
            return v___x_3225_;
        }
        _ => {
            let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3221_);
            crate::leanh::lean_dec(v_h__1_3219_);
            v___x_3226_ = crate::leanh::lean_box(0);
            v___x_3227_ = crate::leanh::lean_apply_1(v_h__2_3220_, v___x_3226_);
            return v___x_3227_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(
    mut v_x_3228_: *mut crate::leanh::LeanObject,
    mut v_h__1_3229_: *mut crate::leanh::LeanObject,
    mut v_h__2_3230_: *mut crate::leanh::LeanObject,
    mut v_h__3_3231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_3232_: u8 = 0;
    let mut v_res_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_3232_ = (crate::leanh::lean_unbox(v_x_3228_) as u8);
    v_res_3233_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_36__boxed_3232_, v_h__1_3229_, v_h__2_3230_, v_h__3_3231_);
    return v_res_3233_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(
    mut v_motive_3234_: *mut crate::leanh::LeanObject,
    mut v_x_3235_: u8,
    mut v_h__1_3236_: *mut crate::leanh::LeanObject,
    mut v_h__2_3237_: *mut crate::leanh::LeanObject,
    mut v_h__3_3238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_3235_ {
        0 => {
            let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3238_);
            crate::leanh::lean_dec(v_h__2_3237_);
            v___x_3239_ = crate::leanh::lean_box(0);
            v___x_3240_ = crate::leanh::lean_apply_1(v_h__1_3236_, v___x_3239_);
            return v___x_3240_;
        }
        1 => {
            let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3237_);
            crate::leanh::lean_dec(v_h__1_3236_);
            v___x_3241_ = crate::leanh::lean_box(0);
            v___x_3242_ = crate::leanh::lean_apply_1(v_h__3_3238_, v___x_3241_);
            return v___x_3242_;
        }
        _ => {
            let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3238_);
            crate::leanh::lean_dec(v_h__1_3236_);
            v___x_3243_ = crate::leanh::lean_box(0);
            v___x_3244_ = crate::leanh::lean_apply_1(v_h__2_3237_, v___x_3243_);
            return v___x_3244_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(
    mut v_motive_3245_: *mut crate::leanh::LeanObject,
    mut v_x_3246_: *mut crate::leanh::LeanObject,
    mut v_h__1_3247_: *mut crate::leanh::LeanObject,
    mut v_h__2_3248_: *mut crate::leanh::LeanObject,
    mut v_h__3_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_3250_: u8 = 0;
    let mut v_res_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_3250_ = (crate::leanh::lean_unbox(v_x_3246_) as u8);
    v_res_3251_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_3245_, v_x_51__boxed_3250_, v_h__1_3247_, v_h__2_3248_, v_h__3_3249_);
    return v_res_3251_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(
    mut v_k_3252_: *mut crate::leanh::LeanObject,
    mut v_f_3253_: *mut crate::leanh::LeanObject,
    mut v_ll_3254_: *mut crate::leanh::LeanObject,
    mut v_m_3255_: *mut crate::leanh::LeanObject,
    mut v_rr_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_3255_) == 0 {
                    v_k_3257_ = crate::leanh::lean_ctor_get(v_m_3255_, 1);
                    crate::leanh::lean_inc_n(v_k_3257_, 2);
                    v_v_3258_ = crate::leanh::lean_ctor_get(v_m_3255_, 2);
                    crate::leanh::lean_inc(v_v_3258_);
                    v_l_3259_ = crate::leanh::lean_ctor_get(v_m_3255_, 3);
                    crate::leanh::lean_inc(v_l_3259_);
                    v_r_3260_ = crate::leanh::lean_ctor_get(v_m_3255_, 4);
                    crate::leanh::lean_inc(v_r_3260_);
                    crate::leanh::lean_dec_ref_known(v_m_3255_, 5);
                    crate::leanh::lean_inc_ref(v_k_3252_);
                    v___x_3261_ = crate::leanh::lean_apply_1(v_k_3252_, v_k_3257_);
                    v___x_3262_ = (crate::leanh::lean_unbox(v___x_3261_) as u8);
                    match v___x_3262_ {
                        0 => {
                            v___x_3263_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3263_, 0, v_k_3257_);
                            crate::leanh::lean_ctor_set(v___x_3263_, 1, v_v_3258_);
                            v___x_3264_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_3260_);
                            crate::leanh::lean_dec(v_r_3260_);
                            v___x_3265_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3265_, 0, v___x_3263_);
                            crate::leanh::lean_ctor_set(v___x_3265_, 1, v___x_3264_);
                            v___x_3266_ = l_List_appendTR___redArg(v___x_3265_, v_rr_3256_);
                            v_m_3255_ = v_l_3259_;
                            v_rr_3256_ = v___x_3266_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec_ref(v_k_3252_);
                            v___x_3268_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_3259_);
                            crate::leanh::lean_dec(v_l_3259_);
                            v___x_3269_ = l_List_appendTR___redArg(v_ll_3254_, v___x_3268_);
                            v___x_3270_ =
                                l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_3257_, v_v_3258_);
                            v___x_3271_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_3260_);
                            crate::leanh::lean_dec(v_r_3260_);
                            v___x_3272_ = l_List_appendTR___redArg(v___x_3271_, v_rr_3256_);
                            v___x_3273_ = crate::leanh::lean_apply_4(
                                v_f_3253_,
                                v___x_3269_,
                                v___x_3270_,
                                crate::leanh::lean_box(0),
                                v___x_3272_,
                            );
                            return v___x_3273_;
                        }
                        _ => {
                            v___x_3274_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_3259_);
                            crate::leanh::lean_dec(v_l_3259_);
                            v___x_3275_ = l_List_appendTR___redArg(v_ll_3254_, v___x_3274_);
                            v___x_3276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3276_, 0, v_k_3257_);
                            crate::leanh::lean_ctor_set(v___x_3276_, 1, v_v_3258_);
                            v___x_3277_ = crate::leanh::lean_box(0);
                            v___x_3278_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3278_, 0, v___x_3276_);
                            crate::leanh::lean_ctor_set(v___x_3278_, 1, v___x_3277_);
                            v___x_3279_ = l_List_appendTR___redArg(v___x_3275_, v___x_3278_);
                            v_ll_3254_ = v___x_3279_;
                            v_m_3255_ = v_r_3260_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_3252_);
                    v___x_3281_ = crate::leanh::lean_box(0);
                    v___x_3282_ = crate::leanh::lean_apply_4(
                        v_f_3253_,
                        v_ll_3254_,
                        v___x_3281_,
                        crate::leanh::lean_box(0),
                        v_rr_3256_,
                    );
                    return v___x_3282_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition_go(
    mut v_00_u03b1_3283_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3284_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3285_: *mut crate::leanh::LeanObject,
    mut v_inst_3286_: *mut crate::leanh::LeanObject,
    mut v_k_3287_: *mut crate::leanh::LeanObject,
    mut v_l_3288_: *mut crate::leanh::LeanObject,
    mut v_f_3289_: *mut crate::leanh::LeanObject,
    mut v_ll_3290_: *mut crate::leanh::LeanObject,
    mut v_m_3291_: *mut crate::leanh::LeanObject,
    mut v_hm_3292_: *mut crate::leanh::LeanObject,
    mut v_rr_3293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3294_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(
        v_k_3287_, v_f_3289_, v_ll_3290_, v_m_3291_, v_rr_3293_,
    );
    return v___x_3294_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(
    mut v_00_u03b1_3295_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3296_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3297_: *mut crate::leanh::LeanObject,
    mut v_inst_3298_: *mut crate::leanh::LeanObject,
    mut v_k_3299_: *mut crate::leanh::LeanObject,
    mut v_l_3300_: *mut crate::leanh::LeanObject,
    mut v_f_3301_: *mut crate::leanh::LeanObject,
    mut v_ll_3302_: *mut crate::leanh::LeanObject,
    mut v_m_3303_: *mut crate::leanh::LeanObject,
    mut v_hm_3304_: *mut crate::leanh::LeanObject,
    mut v_rr_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3306_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go(
        v_00_u03b1_3295_,
        v_00_u03b2_3296_,
        v_00_u03b4_3297_,
        v_inst_3298_,
        v_k_3299_,
        v_l_3300_,
        v_f_3301_,
        v_ll_3302_,
        v_m_3303_,
        v_hm_3304_,
        v_rr_3305_,
    );
    crate::leanh::lean_dec(v_l_3300_);
    crate::leanh::lean_dec_ref(v_inst_3298_);
    return v_res_3306_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(
    mut v_k_3307_: *mut crate::leanh::LeanObject,
    mut v_l_3308_: *mut crate::leanh::LeanObject,
    mut v_f_3309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3310_ = crate::leanh::lean_box(0);
    v___x_3311_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(
        v_k_3307_,
        v_f_3309_,
        v___x_3310_,
        v_l_3308_,
        v___x_3310_,
    );
    return v___x_3311_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition(
    mut v_00_u03b1_3312_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3313_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3314_: *mut crate::leanh::LeanObject,
    mut v_inst_3315_: *mut crate::leanh::LeanObject,
    mut v_k_3316_: *mut crate::leanh::LeanObject,
    mut v_l_3317_: *mut crate::leanh::LeanObject,
    mut v_f_3318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3319_ =
        l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v_k_3316_, v_l_3317_, v_f_3318_);
    return v___x_3319_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(
    mut v_00_u03b1_3320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3321_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3322_: *mut crate::leanh::LeanObject,
    mut v_inst_3323_: *mut crate::leanh::LeanObject,
    mut v_k_3324_: *mut crate::leanh::LeanObject,
    mut v_l_3325_: *mut crate::leanh::LeanObject,
    mut v_f_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_Std_DTreeMap_Internal_Impl_applyPartition(
        v_00_u03b1_3320_,
        v_00_u03b2_3321_,
        v_00_u03b4_3322_,
        v_inst_3323_,
        v_k_3324_,
        v_l_3325_,
        v_f_3326_,
    );
    crate::leanh::lean_dec_ref(v_inst_3323_);
    return v_res_3327_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(
    mut v_f_3328_: *mut crate::leanh::LeanObject,
    mut v_c_3329_: *mut crate::leanh::LeanObject,
    mut v_h_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3331_ = crate::leanh::lean_apply_2(v_f_3328_, v_c_3329_, crate::leanh::lean_box(0));
    return v___x_3331_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
    mut v_inst_3332_: *mut crate::leanh::LeanObject,
    mut v_k_3333_: *mut crate::leanh::LeanObject,
    mut v_l_3334_: *mut crate::leanh::LeanObject,
    mut v_f_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___f_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_3334_) == 0 {
                    v_k_3336_ = crate::leanh::lean_ctor_get(v_l_3334_, 1);
                    crate::leanh::lean_inc_n(v_k_3336_, 2);
                    v_v_3337_ = crate::leanh::lean_ctor_get(v_l_3334_, 2);
                    crate::leanh::lean_inc(v_v_3337_);
                    v_l_3338_ = crate::leanh::lean_ctor_get(v_l_3334_, 3);
                    crate::leanh::lean_inc(v_l_3338_);
                    v_r_3339_ = crate::leanh::lean_ctor_get(v_l_3334_, 4);
                    crate::leanh::lean_inc(v_r_3339_);
                    crate::leanh::lean_dec_ref_known(v_l_3334_, 5);
                    crate::leanh::lean_inc_ref(v_inst_3332_);
                    crate::leanh::lean_inc(v_k_3333_);
                    v___x_3340_ = crate::leanh::lean_apply_2(v_inst_3332_, v_k_3333_, v_k_3336_);
                    v___x_3341_ = (crate::leanh::lean_unbox(v___x_3340_) as u8);
                    match v___x_3341_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_3339_);
                            crate::leanh::lean_dec(v_v_3337_);
                            crate::leanh::lean_dec(v_k_3336_);
                            v___f_3342_ = crate::leanh::lean_alloc_closure(
                                l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0
                                    as *mut core::ffi::c_void,
                                3,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_3342_, 0, v_f_3335_);
                            v_l_3334_ = v_l_3338_;
                            v_f_3335_ = v___f_3342_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_3339_);
                            crate::leanh::lean_dec(v_l_3338_);
                            crate::leanh::lean_dec(v_k_3333_);
                            crate::leanh::lean_dec_ref(v_inst_3332_);
                            v___x_3344_ =
                                l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_3336_, v_v_3337_);
                            v___x_3345_ = crate::leanh::lean_apply_2(
                                v_f_3335_,
                                v___x_3344_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_3345_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_3338_);
                            crate::leanh::lean_dec(v_v_3337_);
                            crate::leanh::lean_dec(v_k_3336_);
                            v___f_3346_ = crate::leanh::lean_alloc_closure(
                                l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0
                                    as *mut core::ffi::c_void,
                                3,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_3346_, 0, v_f_3335_);
                            v_l_3334_ = v_r_3339_;
                            v_f_3335_ = v___f_3346_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3333_);
                    crate::leanh::lean_dec_ref(v_inst_3332_);
                    v___x_3348_ = crate::leanh::lean_box(0);
                    v___x_3349_ = crate::leanh::lean_apply_2(
                        v_f_3335_,
                        v___x_3348_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3349_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyCell(
    mut v_00_u03b1_3350_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3351_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3352_: *mut crate::leanh::LeanObject,
    mut v_inst_3353_: *mut crate::leanh::LeanObject,
    mut v_k_3354_: *mut crate::leanh::LeanObject,
    mut v_l_3355_: *mut crate::leanh::LeanObject,
    mut v_f_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3357_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
        v_inst_3353_,
        v_k_3354_,
        v_l_3355_,
        v_f_3356_,
    );
    return v___x_3357_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(
    mut v_l_3358_: *mut crate::leanh::LeanObject,
    mut v_f_3359_: *mut crate::leanh::LeanObject,
    mut v_h__1_3360_: *mut crate::leanh::LeanObject,
    mut v_h__2_3361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3358_) == 0 {
        let mut v_size_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3360_);
        v_size_3362_ = crate::leanh::lean_ctor_get(v_l_3358_, 0);
        crate::leanh::lean_inc(v_size_3362_);
        v_k_3363_ = crate::leanh::lean_ctor_get(v_l_3358_, 1);
        crate::leanh::lean_inc(v_k_3363_);
        v_v_3364_ = crate::leanh::lean_ctor_get(v_l_3358_, 2);
        crate::leanh::lean_inc(v_v_3364_);
        v_l_3365_ = crate::leanh::lean_ctor_get(v_l_3358_, 3);
        crate::leanh::lean_inc(v_l_3365_);
        v_r_3366_ = crate::leanh::lean_ctor_get(v_l_3358_, 4);
        crate::leanh::lean_inc(v_r_3366_);
        crate::leanh::lean_dec_ref_known(v_l_3358_, 5);
        v___x_3367_ = crate::leanh::lean_apply_6(
            v_h__2_3361_,
            v_size_3362_,
            v_k_3363_,
            v_v_3364_,
            v_l_3365_,
            v_r_3366_,
            v_f_3359_,
        );
        return v___x_3367_;
    } else {
        let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3361_);
        v___x_3368_ = crate::leanh::lean_apply_1(v_h__1_3360_, v_f_3359_);
        return v___x_3368_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(
    mut v_00_u03b1_3369_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3370_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3371_: *mut crate::leanh::LeanObject,
    mut v_inst_3372_: *mut crate::leanh::LeanObject,
    mut v_k_3373_: *mut crate::leanh::LeanObject,
    mut v_motive_3374_: *mut crate::leanh::LeanObject,
    mut v_l_3375_: *mut crate::leanh::LeanObject,
    mut v_f_3376_: *mut crate::leanh::LeanObject,
    mut v_h__1_3377_: *mut crate::leanh::LeanObject,
    mut v_h__2_3378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3375_) == 0 {
        let mut v_size_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3377_);
        v_size_3379_ = crate::leanh::lean_ctor_get(v_l_3375_, 0);
        crate::leanh::lean_inc(v_size_3379_);
        v_k_3380_ = crate::leanh::lean_ctor_get(v_l_3375_, 1);
        crate::leanh::lean_inc(v_k_3380_);
        v_v_3381_ = crate::leanh::lean_ctor_get(v_l_3375_, 2);
        crate::leanh::lean_inc(v_v_3381_);
        v_l_3382_ = crate::leanh::lean_ctor_get(v_l_3375_, 3);
        crate::leanh::lean_inc(v_l_3382_);
        v_r_3383_ = crate::leanh::lean_ctor_get(v_l_3375_, 4);
        crate::leanh::lean_inc(v_r_3383_);
        crate::leanh::lean_dec_ref_known(v_l_3375_, 5);
        v___x_3384_ = crate::leanh::lean_apply_6(
            v_h__2_3378_,
            v_size_3379_,
            v_k_3380_,
            v_v_3381_,
            v_l_3382_,
            v_r_3383_,
            v_f_3376_,
        );
        return v___x_3384_;
    } else {
        let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3378_);
        v___x_3385_ = crate::leanh::lean_apply_1(v_h__1_3377_, v_f_3376_);
        return v___x_3385_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(
    mut v_00_u03b1_3386_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3387_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3388_: *mut crate::leanh::LeanObject,
    mut v_inst_3389_: *mut crate::leanh::LeanObject,
    mut v_k_3390_: *mut crate::leanh::LeanObject,
    mut v_motive_3391_: *mut crate::leanh::LeanObject,
    mut v_l_3392_: *mut crate::leanh::LeanObject,
    mut v_f_3393_: *mut crate::leanh::LeanObject,
    mut v_h__1_3394_: *mut crate::leanh::LeanObject,
    mut v_h__2_3395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3396_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(v_00_u03b1_3386_, v_00_u03b2_3387_, v_00_u03b4_3388_, v_inst_3389_, v_k_3390_, v_motive_3391_, v_l_3392_, v_f_3393_, v_h__1_3394_, v_h__2_3395_);
    crate::leanh::lean_dec(v_k_3390_);
    crate::leanh::lean_dec_ref(v_inst_3389_);
    return v_res_3396_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(
    mut v_x_3397_: u8,
    mut v_h__1_3398_: *mut crate::leanh::LeanObject,
    mut v_h__2_3399_: *mut crate::leanh::LeanObject,
    mut v_h__3_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_3397_ {
        0 => {
            let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3400_);
            crate::leanh::lean_dec(v_h__2_3399_);
            v___x_3401_ = crate::leanh::lean_apply_1(v_h__1_3398_, crate::leanh::lean_box(0));
            return v___x_3401_;
        }
        1 => {
            let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3400_);
            crate::leanh::lean_dec(v_h__1_3398_);
            v___x_3402_ = crate::leanh::lean_apply_1(v_h__2_3399_, crate::leanh::lean_box(0));
            return v___x_3402_;
        }
        _ => {
            let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3399_);
            crate::leanh::lean_dec(v_h__1_3398_);
            v___x_3403_ = crate::leanh::lean_apply_1(v_h__3_3400_, crate::leanh::lean_box(0));
            return v___x_3403_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(
    mut v_x_3404_: *mut crate::leanh::LeanObject,
    mut v_h__1_3405_: *mut crate::leanh::LeanObject,
    mut v_h__2_3406_: *mut crate::leanh::LeanObject,
    mut v_h__3_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_3408_: u8 = 0;
    let mut v_res_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_3408_ = (crate::leanh::lean_unbox(v_x_3404_) as u8);
    v_res_3409_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_3408_, v_h__1_3405_, v_h__2_3406_, v_h__3_3407_);
    return v_res_3409_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(
    mut v_motive_3410_: *mut crate::leanh::LeanObject,
    mut v_x_3411_: u8,
    mut v_h__1_3412_: *mut crate::leanh::LeanObject,
    mut v_h__2_3413_: *mut crate::leanh::LeanObject,
    mut v_h__3_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_3411_ {
        0 => {
            let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3414_);
            crate::leanh::lean_dec(v_h__2_3413_);
            v___x_3415_ = crate::leanh::lean_apply_1(v_h__1_3412_, crate::leanh::lean_box(0));
            return v___x_3415_;
        }
        1 => {
            let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3414_);
            crate::leanh::lean_dec(v_h__1_3412_);
            v___x_3416_ = crate::leanh::lean_apply_1(v_h__2_3413_, crate::leanh::lean_box(0));
            return v___x_3416_;
        }
        _ => {
            let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3413_);
            crate::leanh::lean_dec(v_h__1_3412_);
            v___x_3417_ = crate::leanh::lean_apply_1(v_h__3_3414_, crate::leanh::lean_box(0));
            return v___x_3417_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(
    mut v_motive_3418_: *mut crate::leanh::LeanObject,
    mut v_x_3419_: *mut crate::leanh::LeanObject,
    mut v_h__1_3420_: *mut crate::leanh::LeanObject,
    mut v_h__2_3421_: *mut crate::leanh::LeanObject,
    mut v_h__3_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42__boxed_3423_: u8 = 0;
    let mut v_res_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_3423_ = (crate::leanh::lean_unbox(v_x_3419_) as u8);
    v_res_3424_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_3418_, v_x_42__boxed_3423_, v_h__1_3420_, v_h__2_3421_, v_h__3_3422_);
    return v_res_3424_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(
    mut v_m_3425_: *mut crate::leanh::LeanObject,
    mut v_h__1_3426_: *mut crate::leanh::LeanObject,
    mut v_h__2_3427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_3425_) == 0 {
        let mut v_size_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3426_);
        v_size_3428_ = crate::leanh::lean_ctor_get(v_m_3425_, 0);
        crate::leanh::lean_inc(v_size_3428_);
        v_k_3429_ = crate::leanh::lean_ctor_get(v_m_3425_, 1);
        crate::leanh::lean_inc(v_k_3429_);
        v_v_3430_ = crate::leanh::lean_ctor_get(v_m_3425_, 2);
        crate::leanh::lean_inc(v_v_3430_);
        v_l_3431_ = crate::leanh::lean_ctor_get(v_m_3425_, 3);
        crate::leanh::lean_inc(v_l_3431_);
        v_r_3432_ = crate::leanh::lean_ctor_get(v_m_3425_, 4);
        crate::leanh::lean_inc(v_r_3432_);
        crate::leanh::lean_dec_ref_known(v_m_3425_, 5);
        v___x_3433_ = crate::leanh::lean_apply_6(
            v_h__2_3427_,
            v_size_3428_,
            v_k_3429_,
            v_v_3430_,
            v_l_3431_,
            v_r_3432_,
            crate::leanh::lean_box(0),
        );
        return v___x_3433_;
    } else {
        let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3427_);
        v___x_3434_ = crate::leanh::lean_apply_1(v_h__1_3426_, crate::leanh::lean_box(0));
        return v___x_3434_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(
    mut v_00_u03b1_3435_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3436_: *mut crate::leanh::LeanObject,
    mut v_inst_3437_: *mut crate::leanh::LeanObject,
    mut v_k_3438_: *mut crate::leanh::LeanObject,
    mut v_l_3439_: *mut crate::leanh::LeanObject,
    mut v_motive_3440_: *mut crate::leanh::LeanObject,
    mut v_m_3441_: *mut crate::leanh::LeanObject,
    mut v_hm_3442_: *mut crate::leanh::LeanObject,
    mut v_h__1_3443_: *mut crate::leanh::LeanObject,
    mut v_h__2_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_3441_) == 0 {
        let mut v_size_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3443_);
        v_size_3445_ = crate::leanh::lean_ctor_get(v_m_3441_, 0);
        crate::leanh::lean_inc(v_size_3445_);
        v_k_3446_ = crate::leanh::lean_ctor_get(v_m_3441_, 1);
        crate::leanh::lean_inc(v_k_3446_);
        v_v_3447_ = crate::leanh::lean_ctor_get(v_m_3441_, 2);
        crate::leanh::lean_inc(v_v_3447_);
        v_l_3448_ = crate::leanh::lean_ctor_get(v_m_3441_, 3);
        crate::leanh::lean_inc(v_l_3448_);
        v_r_3449_ = crate::leanh::lean_ctor_get(v_m_3441_, 4);
        crate::leanh::lean_inc(v_r_3449_);
        crate::leanh::lean_dec_ref_known(v_m_3441_, 5);
        v___x_3450_ = crate::leanh::lean_apply_6(
            v_h__2_3444_,
            v_size_3445_,
            v_k_3446_,
            v_v_3447_,
            v_l_3448_,
            v_r_3449_,
            crate::leanh::lean_box(0),
        );
        return v___x_3450_;
    } else {
        let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3444_);
        v___x_3451_ = crate::leanh::lean_apply_1(v_h__1_3443_, crate::leanh::lean_box(0));
        return v___x_3451_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(
    mut v_00_u03b1_3452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3453_: *mut crate::leanh::LeanObject,
    mut v_inst_3454_: *mut crate::leanh::LeanObject,
    mut v_k_3455_: *mut crate::leanh::LeanObject,
    mut v_l_3456_: *mut crate::leanh::LeanObject,
    mut v_motive_3457_: *mut crate::leanh::LeanObject,
    mut v_m_3458_: *mut crate::leanh::LeanObject,
    mut v_hm_3459_: *mut crate::leanh::LeanObject,
    mut v_h__1_3460_: *mut crate::leanh::LeanObject,
    mut v_h__2_3461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(v_00_u03b1_3452_, v_00_u03b2_3453_, v_inst_3454_, v_k_3455_, v_l_3456_, v_motive_3457_, v_m_3458_, v_hm_3459_, v_h__1_3460_, v_h__2_3461_);
    crate::leanh::lean_dec(v_l_3456_);
    crate::leanh::lean_dec_ref(v_k_3455_);
    crate::leanh::lean_dec_ref(v_inst_3454_);
    return v_res_3462_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(
    mut v_x_3463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3463_) {
        0 => {
            let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3464_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3464_;
        }
        1 => {
            let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3465_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3465_;
        }
        _ => {
            let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3466_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3466_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg___boxed(
    mut v_x_3467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(v_x_3467_);
    crate::leanh::lean_dec_ref(v_x_3467_);
    return v_res_3468_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(
    mut v_00_u03b1_3469_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3470_: *mut crate::leanh::LeanObject,
    mut v_inst_3471_: *mut crate::leanh::LeanObject,
    mut v_k_3472_: *mut crate::leanh::LeanObject,
    mut v_x_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3474_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(v_x_3473_);
    return v___x_3474_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___boxed(
    mut v_00_u03b1_3475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3476_: *mut crate::leanh::LeanObject,
    mut v_inst_3477_: *mut crate::leanh::LeanObject,
    mut v_k_3478_: *mut crate::leanh::LeanObject,
    mut v_x_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(
        v_00_u03b1_3475_,
        v_00_u03b2_3476_,
        v_inst_3477_,
        v_k_3478_,
        v_x_3479_,
    );
    crate::leanh::lean_dec_ref(v_x_3479_);
    crate::leanh::lean_dec_ref(v_k_3478_);
    crate::leanh::lean_dec_ref(v_inst_3477_);
    return v_res_3480_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(
    mut v_t_3481_: *mut crate::leanh::LeanObject,
    mut v_k_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_3481_) {
        0 => {
            let mut v_a_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3483_ = crate::leanh::lean_ctor_get(v_t_3481_, 0);
            crate::leanh::lean_inc(v_a_3483_);
            v_a_3484_ = crate::leanh::lean_ctor_get(v_t_3481_, 1);
            crate::leanh::lean_inc(v_a_3484_);
            v_a_3485_ = crate::leanh::lean_ctor_get(v_t_3481_, 2);
            crate::leanh::lean_inc(v_a_3485_);
            crate::leanh::lean_dec_ref_known(v_t_3481_, 3);
            v___x_3486_ = crate::leanh::lean_apply_4(
                v_k_3482_,
                v_a_3483_,
                crate::leanh::lean_box(0),
                v_a_3484_,
                v_a_3485_,
            );
            return v___x_3486_;
        }
        1 => {
            let mut v_a_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3487_ = crate::leanh::lean_ctor_get(v_t_3481_, 0);
            crate::leanh::lean_inc(v_a_3487_);
            v_a_3488_ = crate::leanh::lean_ctor_get(v_t_3481_, 1);
            crate::leanh::lean_inc(v_a_3488_);
            v_a_3489_ = crate::leanh::lean_ctor_get(v_t_3481_, 2);
            crate::leanh::lean_inc(v_a_3489_);
            crate::leanh::lean_dec_ref_known(v_t_3481_, 3);
            v___x_3490_ = crate::leanh::lean_apply_3(v_k_3482_, v_a_3487_, v_a_3488_, v_a_3489_);
            return v___x_3490_;
        }
        _ => {
            let mut v_a_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3491_ = crate::leanh::lean_ctor_get(v_t_3481_, 0);
            crate::leanh::lean_inc(v_a_3491_);
            v_a_3492_ = crate::leanh::lean_ctor_get(v_t_3481_, 1);
            crate::leanh::lean_inc(v_a_3492_);
            v_a_3493_ = crate::leanh::lean_ctor_get(v_t_3481_, 2);
            crate::leanh::lean_inc(v_a_3493_);
            crate::leanh::lean_dec_ref_known(v_t_3481_, 3);
            v___x_3494_ = crate::leanh::lean_apply_4(
                v_k_3482_,
                v_a_3491_,
                v_a_3492_,
                crate::leanh::lean_box(0),
                v_a_3493_,
            );
            return v___x_3494_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(
    mut v_00_u03b1_3495_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3496_: *mut crate::leanh::LeanObject,
    mut v_inst_3497_: *mut crate::leanh::LeanObject,
    mut v_k_3498_: *mut crate::leanh::LeanObject,
    mut v_motive_3499_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3500_: *mut crate::leanh::LeanObject,
    mut v_t_3501_: *mut crate::leanh::LeanObject,
    mut v_h_3502_: *mut crate::leanh::LeanObject,
    mut v_k_3503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3504_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3501_, v_k_3503_);
    return v___x_3504_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___boxed(
    mut v_00_u03b1_3505_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3506_: *mut crate::leanh::LeanObject,
    mut v_inst_3507_: *mut crate::leanh::LeanObject,
    mut v_k_3508_: *mut crate::leanh::LeanObject,
    mut v_motive_3509_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3510_: *mut crate::leanh::LeanObject,
    mut v_t_3511_: *mut crate::leanh::LeanObject,
    mut v_h_3512_: *mut crate::leanh::LeanObject,
    mut v_k_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3514_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(
        v_00_u03b1_3505_,
        v_00_u03b2_3506_,
        v_inst_3507_,
        v_k_3508_,
        v_motive_3509_,
        v_ctorIdx_3510_,
        v_t_3511_,
        v_h_3512_,
        v_k_3513_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3510_);
    crate::leanh::lean_dec_ref(v_k_3508_);
    crate::leanh::lean_dec_ref(v_inst_3507_);
    return v_res_3514_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___redArg(
    mut v_t_3515_: *mut crate::leanh::LeanObject,
    mut v_lt_3516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3517_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3515_, v_lt_3516_);
    return v___x_3517_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(
    mut v_00_u03b1_3518_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3519_: *mut crate::leanh::LeanObject,
    mut v_inst_3520_: *mut crate::leanh::LeanObject,
    mut v_k_3521_: *mut crate::leanh::LeanObject,
    mut v_motive_3522_: *mut crate::leanh::LeanObject,
    mut v_t_3523_: *mut crate::leanh::LeanObject,
    mut v_h_3524_: *mut crate::leanh::LeanObject,
    mut v_lt_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3523_, v_lt_3525_);
    return v___x_3526_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___boxed(
    mut v_00_u03b1_3527_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3528_: *mut crate::leanh::LeanObject,
    mut v_inst_3529_: *mut crate::leanh::LeanObject,
    mut v_k_3530_: *mut crate::leanh::LeanObject,
    mut v_motive_3531_: *mut crate::leanh::LeanObject,
    mut v_t_3532_: *mut crate::leanh::LeanObject,
    mut v_h_3533_: *mut crate::leanh::LeanObject,
    mut v_lt_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3535_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(
        v_00_u03b1_3527_,
        v_00_u03b2_3528_,
        v_inst_3529_,
        v_k_3530_,
        v_motive_3531_,
        v_t_3532_,
        v_h_3533_,
        v_lt_3534_,
    );
    crate::leanh::lean_dec_ref(v_k_3530_);
    crate::leanh::lean_dec_ref(v_inst_3529_);
    return v_res_3535_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___redArg(
    mut v_t_3536_: *mut crate::leanh::LeanObject,
    mut v_eq_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3538_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3536_, v_eq_3537_);
    return v___x_3538_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(
    mut v_00_u03b1_3539_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3540_: *mut crate::leanh::LeanObject,
    mut v_inst_3541_: *mut crate::leanh::LeanObject,
    mut v_k_3542_: *mut crate::leanh::LeanObject,
    mut v_motive_3543_: *mut crate::leanh::LeanObject,
    mut v_t_3544_: *mut crate::leanh::LeanObject,
    mut v_h_3545_: *mut crate::leanh::LeanObject,
    mut v_eq_3546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3547_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3544_, v_eq_3546_);
    return v___x_3547_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___boxed(
    mut v_00_u03b1_3548_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3549_: *mut crate::leanh::LeanObject,
    mut v_inst_3550_: *mut crate::leanh::LeanObject,
    mut v_k_3551_: *mut crate::leanh::LeanObject,
    mut v_motive_3552_: *mut crate::leanh::LeanObject,
    mut v_t_3553_: *mut crate::leanh::LeanObject,
    mut v_h_3554_: *mut crate::leanh::LeanObject,
    mut v_eq_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(
        v_00_u03b1_3548_,
        v_00_u03b2_3549_,
        v_inst_3550_,
        v_k_3551_,
        v_motive_3552_,
        v_t_3553_,
        v_h_3554_,
        v_eq_3555_,
    );
    crate::leanh::lean_dec_ref(v_k_3551_);
    crate::leanh::lean_dec_ref(v_inst_3550_);
    return v_res_3556_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___redArg(
    mut v_t_3557_: *mut crate::leanh::LeanObject,
    mut v_gt_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3559_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3557_, v_gt_3558_);
    return v___x_3559_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(
    mut v_00_u03b1_3560_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3561_: *mut crate::leanh::LeanObject,
    mut v_inst_3562_: *mut crate::leanh::LeanObject,
    mut v_k_3563_: *mut crate::leanh::LeanObject,
    mut v_motive_3564_: *mut crate::leanh::LeanObject,
    mut v_t_3565_: *mut crate::leanh::LeanObject,
    mut v_h_3566_: *mut crate::leanh::LeanObject,
    mut v_gt_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3565_, v_gt_3567_);
    return v___x_3568_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___boxed(
    mut v_00_u03b1_3569_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3570_: *mut crate::leanh::LeanObject,
    mut v_inst_3571_: *mut crate::leanh::LeanObject,
    mut v_k_3572_: *mut crate::leanh::LeanObject,
    mut v_motive_3573_: *mut crate::leanh::LeanObject,
    mut v_t_3574_: *mut crate::leanh::LeanObject,
    mut v_h_3575_: *mut crate::leanh::LeanObject,
    mut v_gt_3576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3577_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(
        v_00_u03b1_3569_,
        v_00_u03b2_3570_,
        v_inst_3571_,
        v_k_3572_,
        v_motive_3573_,
        v_t_3574_,
        v_h_3575_,
        v_gt_3576_,
    );
    crate::leanh::lean_dec_ref(v_k_3572_);
    crate::leanh::lean_dec_ref(v_inst_3571_);
    return v_res_3577_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_explore___redArg(
    mut v_k_3581_: *mut crate::leanh::LeanObject,
    mut v_init_3582_: *mut crate::leanh::LeanObject,
    mut v_inner_3583_: *mut crate::leanh::LeanObject,
    mut v_l_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_3584_) == 0 {
                    v_k_3585_ = crate::leanh::lean_ctor_get(v_l_3584_, 1);
                    crate::leanh::lean_inc_n(v_k_3585_, 2);
                    v_v_3586_ = crate::leanh::lean_ctor_get(v_l_3584_, 2);
                    crate::leanh::lean_inc(v_v_3586_);
                    v_l_3587_ = crate::leanh::lean_ctor_get(v_l_3584_, 3);
                    crate::leanh::lean_inc(v_l_3587_);
                    v_r_3588_ = crate::leanh::lean_ctor_get(v_l_3584_, 4);
                    crate::leanh::lean_inc(v_r_3588_);
                    crate::leanh::lean_dec_ref_known(v_l_3584_, 5);
                    crate::leanh::lean_inc_ref(v_k_3581_);
                    v___x_3589_ = crate::leanh::lean_apply_1(v_k_3581_, v_k_3585_);
                    v___x_3590_ = (crate::leanh::lean_unbox(v___x_3589_) as u8);
                    match v___x_3590_ {
                        0 => {
                            v___x_3591_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_3588_);
                            crate::leanh::lean_dec(v_r_3588_);
                            v___x_3592_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3592_, 0, v_k_3585_);
                            crate::leanh::lean_ctor_set(v___x_3592_, 1, v_v_3586_);
                            crate::leanh::lean_ctor_set(v___x_3592_, 2, v___x_3591_);
                            crate::leanh::lean_inc(v_inner_3583_);
                            v___x_3593_ = crate::leanh::lean_apply_2(
                                v_inner_3583_,
                                v_init_3582_,
                                v___x_3592_,
                            );
                            v_init_3582_ = v___x_3593_;
                            v_l_3584_ = v_l_3587_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec_ref(v_k_3581_);
                            v___x_3595_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_3587_);
                            crate::leanh::lean_dec(v_l_3587_);
                            v___x_3596_ =
                                l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_3585_, v_v_3586_);
                            v___x_3597_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_3588_);
                            crate::leanh::lean_dec(v_r_3588_);
                            v___x_3598_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3598_, 0, v___x_3595_);
                            crate::leanh::lean_ctor_set(v___x_3598_, 1, v___x_3596_);
                            crate::leanh::lean_ctor_set(v___x_3598_, 2, v___x_3597_);
                            v___x_3599_ = crate::leanh::lean_apply_2(
                                v_inner_3583_,
                                v_init_3582_,
                                v___x_3598_,
                            );
                            return v___x_3599_;
                        }
                        _ => {
                            v___x_3600_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_3587_);
                            crate::leanh::lean_dec(v_l_3587_);
                            v___x_3601_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3601_, 0, v___x_3600_);
                            crate::leanh::lean_ctor_set(v___x_3601_, 1, v_k_3585_);
                            crate::leanh::lean_ctor_set(v___x_3601_, 2, v_v_3586_);
                            crate::leanh::lean_inc(v_inner_3583_);
                            v___x_3602_ = crate::leanh::lean_apply_2(
                                v_inner_3583_,
                                v_init_3582_,
                                v___x_3601_,
                            );
                            v_init_3582_ = v___x_3602_;
                            v_l_3584_ = v_r_3588_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_3581_);
                    v___x_3604_ = l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0;
                    v___x_3605_ =
                        crate::leanh::lean_apply_2(v_inner_3583_, v_init_3582_, v___x_3604_);
                    return v___x_3605_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_explore(
    mut v_00_u03b1_3606_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3607_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3608_: *mut crate::leanh::LeanObject,
    mut v_inst_3609_: *mut crate::leanh::LeanObject,
    mut v_k_3610_: *mut crate::leanh::LeanObject,
    mut v_init_3611_: *mut crate::leanh::LeanObject,
    mut v_inner_3612_: *mut crate::leanh::LeanObject,
    mut v_l_3613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(
        v_k_3610_,
        v_init_3611_,
        v_inner_3612_,
        v_l_3613_,
    );
    return v___x_3614_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_explore___boxed(
    mut v_00_u03b1_3615_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3616_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3617_: *mut crate::leanh::LeanObject,
    mut v_inst_3618_: *mut crate::leanh::LeanObject,
    mut v_k_3619_: *mut crate::leanh::LeanObject,
    mut v_init_3620_: *mut crate::leanh::LeanObject,
    mut v_inner_3621_: *mut crate::leanh::LeanObject,
    mut v_l_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3623_ = l_Std_DTreeMap_Internal_Impl_explore(
        v_00_u03b1_3615_,
        v_00_u03b2_3616_,
        v_00_u03b3_3617_,
        v_inst_3618_,
        v_k_3619_,
        v_init_3620_,
        v_inner_3621_,
        v_l_3622_,
    );
    crate::leanh::lean_dec_ref(v_inst_3618_);
    return v_res_3623_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(
    mut v_c_3624_: *mut crate::leanh::LeanObject,
    mut v_x_3625_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3626_: u8 = 0;
    v___x_3626_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_3624_);
    return v___x_3626_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(
    mut v_c_3627_: *mut crate::leanh::LeanObject,
    mut v_x_3628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3629_: u8 = 0;
    let mut v_r_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3629_ =
        l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(v_c_3627_, v_x_3628_);
    crate::leanh::lean_dec(v_c_3627_);
    v_r_3630_ = crate::leanh::lean_box((v_res_3629_) as usize);
    return v_r_3630_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(
    mut v_inst_3632_: *mut crate::leanh::LeanObject,
    mut v_l_3633_: *mut crate::leanh::LeanObject,
    mut v_k_3634_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: u8 = 0;
    v___f_3635_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0;
    v___x_3636_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
        v_inst_3632_,
        v_k_3634_,
        v_l_3633_,
        v___f_3635_,
    );
    v___x_3637_ = (crate::leanh::lean_unbox(v___x_3636_) as u8);
    crate::leanh::lean_dec(v___x_3636_);
    return v___x_3637_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___boxed(
    mut v_inst_3638_: *mut crate::leanh::LeanObject,
    mut v_l_3639_: *mut crate::leanh::LeanObject,
    mut v_k_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3641_: u8 = 0;
    let mut v_r_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3641_ =
        l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_3638_, v_l_3639_, v_k_3640_);
    v_r_3642_ = crate::leanh::lean_box((v_res_3641_) as usize);
    return v_r_3642_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098(
    mut v_00_u03b1_3643_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3644_: *mut crate::leanh::LeanObject,
    mut v_inst_3645_: *mut crate::leanh::LeanObject,
    mut v_l_3646_: *mut crate::leanh::LeanObject,
    mut v_k_3647_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3648_: u8 = 0;
    v___x_3648_ =
        l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_3645_, v_l_3646_, v_k_3647_);
    return v___x_3648_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(
    mut v_00_u03b1_3649_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3650_: *mut crate::leanh::LeanObject,
    mut v_inst_3651_: *mut crate::leanh::LeanObject,
    mut v_l_3652_: *mut crate::leanh::LeanObject,
    mut v_k_3653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3654_: u8 = 0;
    let mut v_r_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3654_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(
        v_00_u03b1_3649_,
        v_00_u03b2_3650_,
        v_inst_3651_,
        v_l_3652_,
        v_k_3653_,
    );
    v_r_3655_ = crate::leanh::lean_box((v_res_3654_) as usize);
    return v_r_3655_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(
    mut v_c_3656_: *mut crate::leanh::LeanObject,
    mut v_x_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3658_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_3656_);
    return v___x_3658_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(
    mut v_inst_3660_: *mut crate::leanh::LeanObject,
    mut v_l_3661_: *mut crate::leanh::LeanObject,
    mut v_k_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3663_ = l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0;
    v___x_3664_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
        v_inst_3660_,
        v_k_3662_,
        v_l_3661_,
        v___f_3663_,
    );
    return v___x_3664_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f_u2098(
    mut v_00_u03b1_3665_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3666_: *mut crate::leanh::LeanObject,
    mut v_inst_3667_: *mut crate::leanh::LeanObject,
    mut v_inst_3668_: *mut crate::leanh::LeanObject,
    mut v_inst_3669_: *mut crate::leanh::LeanObject,
    mut v_l_3670_: *mut crate::leanh::LeanObject,
    mut v_k_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_3667_, v_l_3670_, v_k_3671_);
    return v___x_3672_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(
    mut v_inst_3673_: *mut crate::leanh::LeanObject,
    mut v_l_3674_: *mut crate::leanh::LeanObject,
    mut v_k_3675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3676_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_3673_, v_l_3674_, v_k_3675_);
    v_val_3677_ = crate::leanh::lean_ctor_get(v___x_3676_, 0);
    crate::leanh::lean_inc(v_val_3677_);
    crate::leanh::lean_dec(v___x_3676_);
    return v_val_3677_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_u2098(
    mut v_00_u03b1_3678_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3679_: *mut crate::leanh::LeanObject,
    mut v_inst_3680_: *mut crate::leanh::LeanObject,
    mut v_inst_3681_: *mut crate::leanh::LeanObject,
    mut v_inst_3682_: *mut crate::leanh::LeanObject,
    mut v_l_3683_: *mut crate::leanh::LeanObject,
    mut v_k_3684_: *mut crate::leanh::LeanObject,
    mut v_h_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3686_ =
        l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(v_inst_3680_, v_l_3683_, v_k_3684_);
    return v___x_3686_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3690_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2;
    v___x_3691_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_3692_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_3693_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1;
    v___x_3694_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0;
    v___x_3695_ = l_mkPanicMessageWithDecl(
        v___x_3694_,
        v___x_3693_,
        v___x_3692_,
        v___x_3691_,
        v___x_3690_,
    );
    return v___x_3695_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(
    mut v_inst_3696_: *mut crate::leanh::LeanObject,
    mut v_l_3697_: *mut crate::leanh::LeanObject,
    mut v_k_3698_: *mut crate::leanh::LeanObject,
    mut v_inst_3699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_3696_, v_l_3697_, v_k_3698_);
    if crate::leanh::lean_obj_tag(v___x_3700_) == 0 {
        let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3701_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3,
        );
        v___x_3702_ = l_panic___redArg(v_inst_3699_, v___x_3701_);
        return v___x_3702_;
    } else {
        let mut v_val_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3703_ = crate::leanh::lean_ctor_get(v___x_3700_, 0);
        crate::leanh::lean_inc(v_val_3703_);
        crate::leanh::lean_dec_ref_known(v___x_3700_, 1);
        return v_val_3703_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___boxed(
    mut v_inst_3704_: *mut crate::leanh::LeanObject,
    mut v_l_3705_: *mut crate::leanh::LeanObject,
    mut v_k_3706_: *mut crate::leanh::LeanObject,
    mut v_inst_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3708_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(
        v_inst_3704_,
        v_l_3705_,
        v_k_3706_,
        v_inst_3707_,
    );
    crate::leanh::lean_dec(v_inst_3707_);
    return v_res_3708_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21_u2098(
    mut v_00_u03b1_3709_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3710_: *mut crate::leanh::LeanObject,
    mut v_inst_3711_: *mut crate::leanh::LeanObject,
    mut v_inst_3712_: *mut crate::leanh::LeanObject,
    mut v_inst_3713_: *mut crate::leanh::LeanObject,
    mut v_l_3714_: *mut crate::leanh::LeanObject,
    mut v_k_3715_: *mut crate::leanh::LeanObject,
    mut v_inst_3716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(
        v_inst_3711_,
        v_l_3714_,
        v_k_3715_,
        v_inst_3716_,
    );
    return v___x_3717_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21_u2098___boxed(
    mut v_00_u03b1_3718_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3719_: *mut crate::leanh::LeanObject,
    mut v_inst_3720_: *mut crate::leanh::LeanObject,
    mut v_inst_3721_: *mut crate::leanh::LeanObject,
    mut v_inst_3722_: *mut crate::leanh::LeanObject,
    mut v_l_3723_: *mut crate::leanh::LeanObject,
    mut v_k_3724_: *mut crate::leanh::LeanObject,
    mut v_inst_3725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3726_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098(
        v_00_u03b1_3718_,
        v_00_u03b2_3719_,
        v_inst_3720_,
        v_inst_3721_,
        v_inst_3722_,
        v_l_3723_,
        v_k_3724_,
        v_inst_3725_,
    );
    crate::leanh::lean_dec(v_inst_3725_);
    return v_res_3726_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(
    mut v_inst_3727_: *mut crate::leanh::LeanObject,
    mut v_k_3728_: *mut crate::leanh::LeanObject,
    mut v_l_3729_: *mut crate::leanh::LeanObject,
    mut v_fallback_3730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3731_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_3727_, v_l_3729_, v_k_3728_);
    if crate::leanh::lean_obj_tag(v___x_3731_) == 0 {
        crate::leanh::lean_inc(v_fallback_3730_);
        return v_fallback_3730_;
    } else {
        let mut v_val_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3732_ = crate::leanh::lean_ctor_get(v___x_3731_, 0);
        crate::leanh::lean_inc(v_val_3732_);
        crate::leanh::lean_dec_ref_known(v___x_3731_, 1);
        return v_val_3732_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(
    mut v_inst_3733_: *mut crate::leanh::LeanObject,
    mut v_k_3734_: *mut crate::leanh::LeanObject,
    mut v_l_3735_: *mut crate::leanh::LeanObject,
    mut v_fallback_3736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3737_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(
        v_inst_3733_,
        v_k_3734_,
        v_l_3735_,
        v_fallback_3736_,
    );
    crate::leanh::lean_dec(v_fallback_3736_);
    return v_res_3737_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD_u2098(
    mut v_00_u03b1_3738_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3739_: *mut crate::leanh::LeanObject,
    mut v_inst_3740_: *mut crate::leanh::LeanObject,
    mut v_inst_3741_: *mut crate::leanh::LeanObject,
    mut v_inst_3742_: *mut crate::leanh::LeanObject,
    mut v_k_3743_: *mut crate::leanh::LeanObject,
    mut v_l_3744_: *mut crate::leanh::LeanObject,
    mut v_fallback_3745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(
        v_inst_3740_,
        v_k_3743_,
        v_l_3744_,
        v_fallback_3745_,
    );
    return v___x_3746_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(
    mut v_00_u03b1_3747_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3748_: *mut crate::leanh::LeanObject,
    mut v_inst_3749_: *mut crate::leanh::LeanObject,
    mut v_inst_3750_: *mut crate::leanh::LeanObject,
    mut v_inst_3751_: *mut crate::leanh::LeanObject,
    mut v_k_3752_: *mut crate::leanh::LeanObject,
    mut v_l_3753_: *mut crate::leanh::LeanObject,
    mut v_fallback_3754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3755_ = l_Std_DTreeMap_Internal_Impl_getD_u2098(
        v_00_u03b1_3747_,
        v_00_u03b2_3748_,
        v_inst_3749_,
        v_inst_3750_,
        v_inst_3751_,
        v_k_3752_,
        v_l_3753_,
        v_fallback_3754_,
    );
    crate::leanh::lean_dec(v_fallback_3754_);
    return v_res_3755_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(
    mut v_c_3756_: *mut crate::leanh::LeanObject,
    mut v_x_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3758_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_3756_);
    return v___x_3758_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
    mut v_inst_3760_: *mut crate::leanh::LeanObject,
    mut v_l_3761_: *mut crate::leanh::LeanObject,
    mut v_k_3762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3763_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0;
    v___x_3764_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
        v_inst_3760_,
        v_k_3762_,
        v_l_3761_,
        v___f_3763_,
    );
    return v___x_3764_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098(
    mut v_00_u03b1_3765_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3766_: *mut crate::leanh::LeanObject,
    mut v_inst_3767_: *mut crate::leanh::LeanObject,
    mut v_l_3768_: *mut crate::leanh::LeanObject,
    mut v_k_3769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3770_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
        v_inst_3767_,
        v_l_3768_,
        v_k_3769_,
    );
    return v___x_3770_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(
    mut v_inst_3771_: *mut crate::leanh::LeanObject,
    mut v_l_3772_: *mut crate::leanh::LeanObject,
    mut v_k_3773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3774_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
        v_inst_3771_,
        v_l_3772_,
        v_k_3773_,
    );
    v_val_3775_ = crate::leanh::lean_ctor_get(v___x_3774_, 0);
    crate::leanh::lean_inc(v_val_3775_);
    crate::leanh::lean_dec(v___x_3774_);
    return v_val_3775_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_u2098(
    mut v_00_u03b1_3776_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3777_: *mut crate::leanh::LeanObject,
    mut v_inst_3778_: *mut crate::leanh::LeanObject,
    mut v_l_3779_: *mut crate::leanh::LeanObject,
    mut v_k_3780_: *mut crate::leanh::LeanObject,
    mut v_h_3781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3782_ =
        l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_3778_, v_l_3779_, v_k_3780_);
    return v___x_3782_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(
    mut v_inst_3783_: *mut crate::leanh::LeanObject,
    mut v_inst_3784_: *mut crate::leanh::LeanObject,
    mut v_l_3785_: *mut crate::leanh::LeanObject,
    mut v_k_3786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3787_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
        v_inst_3783_,
        v_l_3785_,
        v_k_3786_,
    );
    if crate::leanh::lean_obj_tag(v___x_3787_) == 0 {
        let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3788_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3,
        );
        v___x_3789_ = l_panic___redArg(v_inst_3784_, v___x_3788_);
        return v___x_3789_;
    } else {
        let mut v_val_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3790_ = crate::leanh::lean_ctor_get(v___x_3787_, 0);
        crate::leanh::lean_inc(v_val_3790_);
        crate::leanh::lean_dec_ref_known(v___x_3787_, 1);
        return v_val_3790_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg___boxed(
    mut v_inst_3791_: *mut crate::leanh::LeanObject,
    mut v_inst_3792_: *mut crate::leanh::LeanObject,
    mut v_l_3793_: *mut crate::leanh::LeanObject,
    mut v_k_3794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3795_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(
        v_inst_3791_,
        v_inst_3792_,
        v_l_3793_,
        v_k_3794_,
    );
    crate::leanh::lean_dec_ref(v_inst_3792_);
    return v_res_3795_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(
    mut v_00_u03b1_3796_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3797_: *mut crate::leanh::LeanObject,
    mut v_inst_3798_: *mut crate::leanh::LeanObject,
    mut v_inst_3799_: *mut crate::leanh::LeanObject,
    mut v_l_3800_: *mut crate::leanh::LeanObject,
    mut v_k_3801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3802_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(
        v_inst_3798_,
        v_inst_3799_,
        v_l_3800_,
        v_k_3801_,
    );
    return v___x_3802_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___boxed(
    mut v_00_u03b1_3803_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3804_: *mut crate::leanh::LeanObject,
    mut v_inst_3805_: *mut crate::leanh::LeanObject,
    mut v_inst_3806_: *mut crate::leanh::LeanObject,
    mut v_l_3807_: *mut crate::leanh::LeanObject,
    mut v_k_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3809_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(
        v_00_u03b1_3803_,
        v_00_u03b2_3804_,
        v_inst_3805_,
        v_inst_3806_,
        v_l_3807_,
        v_k_3808_,
    );
    crate::leanh::lean_dec_ref(v_inst_3806_);
    return v_res_3809_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(
    mut v_inst_3810_: *mut crate::leanh::LeanObject,
    mut v_k_3811_: *mut crate::leanh::LeanObject,
    mut v_l_3812_: *mut crate::leanh::LeanObject,
    mut v_fallback_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
        v_inst_3810_,
        v_l_3812_,
        v_k_3811_,
    );
    if crate::leanh::lean_obj_tag(v___x_3814_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3813_);
        return v_fallback_3813_;
    } else {
        let mut v_val_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3815_ = crate::leanh::lean_ctor_get(v___x_3814_, 0);
        crate::leanh::lean_inc(v_val_3815_);
        crate::leanh::lean_dec_ref_known(v___x_3814_, 1);
        return v_val_3815_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(
    mut v_inst_3816_: *mut crate::leanh::LeanObject,
    mut v_k_3817_: *mut crate::leanh::LeanObject,
    mut v_l_3818_: *mut crate::leanh::LeanObject,
    mut v_fallback_3819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3820_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(
        v_inst_3816_,
        v_k_3817_,
        v_l_3818_,
        v_fallback_3819_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3819_);
    return v_res_3820_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(
    mut v_00_u03b1_3821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3822_: *mut crate::leanh::LeanObject,
    mut v_inst_3823_: *mut crate::leanh::LeanObject,
    mut v_k_3824_: *mut crate::leanh::LeanObject,
    mut v_l_3825_: *mut crate::leanh::LeanObject,
    mut v_fallback_3826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(
        v_inst_3823_,
        v_k_3824_,
        v_l_3825_,
        v_fallback_3826_,
    );
    return v___x_3827_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(
    mut v_00_u03b1_3828_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3829_: *mut crate::leanh::LeanObject,
    mut v_inst_3830_: *mut crate::leanh::LeanObject,
    mut v_k_3831_: *mut crate::leanh::LeanObject,
    mut v_l_3832_: *mut crate::leanh::LeanObject,
    mut v_fallback_3833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3834_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(
        v_00_u03b1_3828_,
        v_00_u03b2_3829_,
        v_inst_3830_,
        v_k_3831_,
        v_l_3832_,
        v_fallback_3833_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3833_);
    return v_res_3834_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(
    mut v_c_3835_: *mut crate::leanh::LeanObject,
    mut v_x_3836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3837_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_3835_);
    return v___x_3837_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(
    mut v_inst_3839_: *mut crate::leanh::LeanObject,
    mut v_l_3840_: *mut crate::leanh::LeanObject,
    mut v_k_3841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3842_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0;
    v___x_3843_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
        v_inst_3839_,
        v_k_3841_,
        v_l_3840_,
        v___f_3842_,
    );
    return v___x_3843_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098(
    mut v_00_u03b1_3844_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3845_: *mut crate::leanh::LeanObject,
    mut v_inst_3846_: *mut crate::leanh::LeanObject,
    mut v_l_3847_: *mut crate::leanh::LeanObject,
    mut v_k_3848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3849_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_3846_, v_l_3847_, v_k_3848_);
    return v___x_3849_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(
    mut v_inst_3850_: *mut crate::leanh::LeanObject,
    mut v_l_3851_: *mut crate::leanh::LeanObject,
    mut v_k_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_3850_, v_l_3851_, v_k_3852_);
    v_val_3854_ = crate::leanh::lean_ctor_get(v___x_3853_, 0);
    crate::leanh::lean_inc(v_val_3854_);
    crate::leanh::lean_dec(v___x_3853_);
    return v_val_3854_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_u2098(
    mut v_00_u03b1_3855_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3856_: *mut crate::leanh::LeanObject,
    mut v_inst_3857_: *mut crate::leanh::LeanObject,
    mut v_l_3858_: *mut crate::leanh::LeanObject,
    mut v_k_3859_: *mut crate::leanh::LeanObject,
    mut v_h_3860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3861_ =
        l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_3857_, v_l_3858_, v_k_3859_);
    return v___x_3861_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(
    mut v_inst_3862_: *mut crate::leanh::LeanObject,
    mut v_l_3863_: *mut crate::leanh::LeanObject,
    mut v_k_3864_: *mut crate::leanh::LeanObject,
    mut v_inst_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3866_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_3862_, v_l_3863_, v_k_3864_);
    if crate::leanh::lean_obj_tag(v___x_3866_) == 0 {
        let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3867_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3,
        );
        v___x_3868_ = l_panic___redArg(v_inst_3865_, v___x_3867_);
        return v___x_3868_;
    } else {
        let mut v_val_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3869_ = crate::leanh::lean_ctor_get(v___x_3866_, 0);
        crate::leanh::lean_inc(v_val_3869_);
        crate::leanh::lean_dec_ref_known(v___x_3866_, 1);
        return v_val_3869_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg___boxed(
    mut v_inst_3870_: *mut crate::leanh::LeanObject,
    mut v_l_3871_: *mut crate::leanh::LeanObject,
    mut v_k_3872_: *mut crate::leanh::LeanObject,
    mut v_inst_3873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3874_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(
        v_inst_3870_,
        v_l_3871_,
        v_k_3872_,
        v_inst_3873_,
    );
    crate::leanh::lean_dec(v_inst_3873_);
    return v_res_3874_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(
    mut v_00_u03b1_3875_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3876_: *mut crate::leanh::LeanObject,
    mut v_inst_3877_: *mut crate::leanh::LeanObject,
    mut v_l_3878_: *mut crate::leanh::LeanObject,
    mut v_k_3879_: *mut crate::leanh::LeanObject,
    mut v_inst_3880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3881_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(
        v_inst_3877_,
        v_l_3878_,
        v_k_3879_,
        v_inst_3880_,
    );
    return v___x_3881_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___boxed(
    mut v_00_u03b1_3882_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3883_: *mut crate::leanh::LeanObject,
    mut v_inst_3884_: *mut crate::leanh::LeanObject,
    mut v_l_3885_: *mut crate::leanh::LeanObject,
    mut v_k_3886_: *mut crate::leanh::LeanObject,
    mut v_inst_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3888_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(
        v_00_u03b1_3882_,
        v_00_u03b2_3883_,
        v_inst_3884_,
        v_l_3885_,
        v_k_3886_,
        v_inst_3887_,
    );
    crate::leanh::lean_dec(v_inst_3887_);
    return v_res_3888_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(
    mut v_inst_3889_: *mut crate::leanh::LeanObject,
    mut v_k_3890_: *mut crate::leanh::LeanObject,
    mut v_l_3891_: *mut crate::leanh::LeanObject,
    mut v_fallback_3892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3893_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_3889_, v_l_3891_, v_k_3890_);
    if crate::leanh::lean_obj_tag(v___x_3893_) == 0 {
        crate::leanh::lean_inc(v_fallback_3892_);
        return v_fallback_3892_;
    } else {
        let mut v_val_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3894_ = crate::leanh::lean_ctor_get(v___x_3893_, 0);
        crate::leanh::lean_inc(v_val_3894_);
        crate::leanh::lean_dec_ref_known(v___x_3893_, 1);
        return v_val_3894_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(
    mut v_inst_3895_: *mut crate::leanh::LeanObject,
    mut v_k_3896_: *mut crate::leanh::LeanObject,
    mut v_l_3897_: *mut crate::leanh::LeanObject,
    mut v_fallback_3898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3899_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(
        v_inst_3895_,
        v_k_3896_,
        v_l_3897_,
        v_fallback_3898_,
    );
    crate::leanh::lean_dec(v_fallback_3898_);
    return v_res_3899_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(
    mut v_00_u03b1_3900_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3901_: *mut crate::leanh::LeanObject,
    mut v_inst_3902_: *mut crate::leanh::LeanObject,
    mut v_k_3903_: *mut crate::leanh::LeanObject,
    mut v_l_3904_: *mut crate::leanh::LeanObject,
    mut v_fallback_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3906_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(
        v_inst_3902_,
        v_k_3903_,
        v_l_3904_,
        v_fallback_3905_,
    );
    return v___x_3906_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(
    mut v_00_u03b1_3907_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3908_: *mut crate::leanh::LeanObject,
    mut v_inst_3909_: *mut crate::leanh::LeanObject,
    mut v_k_3910_: *mut crate::leanh::LeanObject,
    mut v_l_3911_: *mut crate::leanh::LeanObject,
    mut v_fallback_3912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(
        v_00_u03b1_3907_,
        v_00_u03b2_3908_,
        v_inst_3909_,
        v_k_3910_,
        v_l_3911_,
        v_fallback_3912_,
    );
    crate::leanh::lean_dec(v_fallback_3912_);
    return v_res_3913_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(
    mut v_x_3914_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3915_: u8 = 0;
    v___x_3915_ = 0;
    return v___x_3915_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(
    mut v_x_3916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3917_: u8 = 0;
    let mut v_r_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3917_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_3916_);
    crate::leanh::lean_dec(v_x_3916_);
    v_r_3918_ = crate::leanh::lean_box((v_res_3917_) as usize);
    return v_r_3918_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(
    mut v_sofar_3919_: *mut crate::leanh::LeanObject,
    mut v_step_3920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_step_3920_) == 0 {
        let mut v_a_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3921_ = crate::leanh::lean_ctor_get(v_step_3920_, 0);
        v_a_3922_ = crate::leanh::lean_ctor_get(v_step_3920_, 1);
        crate::leanh::lean_inc(v_a_3922_);
        crate::leanh::lean_inc(v_a_3921_);
        v___x_3923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3923_, 0, v_a_3921_);
        crate::leanh::lean_ctor_set(v___x_3923_, 1, v_a_3922_);
        v___x_3924_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3924_, 0, v___x_3923_);
        return v___x_3924_;
    } else {
        let mut v_a_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3925_ = crate::leanh::lean_ctor_get(v_step_3920_, 2);
        v___x_3926_ = l_List_head_x3f___redArg(v_a_3925_);
        if crate::leanh::lean_obj_tag(v___x_3926_) == 0 {
            crate::leanh::lean_inc(v_sofar_3919_);
            return v_sofar_3919_;
        } else {
            return v___x_3926_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(
    mut v_sofar_3927_: *mut crate::leanh::LeanObject,
    mut v_step_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(
        v_sofar_3927_,
        v_step_3928_,
    );
    crate::leanh::lean_dec_ref(v_step_3928_);
    crate::leanh::lean_dec(v_sofar_3927_);
    return v_res_3929_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(
    mut v_l_3932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3933_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0;
    v___f_3934_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1;
    v___x_3935_ = crate::leanh::lean_box(0);
    v___x_3936_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(
        v___f_3933_,
        v___x_3935_,
        v___f_3934_,
        v_l_3932_,
    );
    return v___x_3936_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(
    mut v_00_u03b1_3937_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3938_: *mut crate::leanh::LeanObject,
    mut v_inst_3939_: *mut crate::leanh::LeanObject,
    mut v_l_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3941_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_3940_);
    return v___x_3941_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(
    mut v_00_u03b1_3942_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3943_: *mut crate::leanh::LeanObject,
    mut v_inst_3944_: *mut crate::leanh::LeanObject,
    mut v_l_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3946_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(
        v_00_u03b1_3942_,
        v_00_u03b2_3943_,
        v_inst_3944_,
        v_l_3945_,
    );
    crate::leanh::lean_dec_ref(v_inst_3944_);
    return v_res_3946_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(
    mut v_x_3947_: *mut crate::leanh::LeanObject,
    mut v_x_3948_: *mut crate::leanh::LeanObject,
    mut v_x_3949_: *mut crate::leanh::LeanObject,
    mut v_r_3950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_List_head_x3f___redArg(v_r_3950_);
    return v___x_3951_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(
    mut v_x_3952_: *mut crate::leanh::LeanObject,
    mut v_x_3953_: *mut crate::leanh::LeanObject,
    mut v_x_3954_: *mut crate::leanh::LeanObject,
    mut v_r_3955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(
        v_x_3952_, v_x_3953_, v_x_3954_, v_r_3955_,
    );
    crate::leanh::lean_dec(v_r_3955_);
    crate::leanh::lean_dec(v_x_3953_);
    crate::leanh::lean_dec(v_x_3952_);
    return v_res_3956_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(
    mut v_l_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3959_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0;
    v___f_3960_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0;
    v___x_3961_ =
        l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_3959_, v_l_3958_, v___f_3960_);
    return v___x_3961_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(
    mut v_00_u03b1_3962_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3963_: *mut crate::leanh::LeanObject,
    mut v_inst_3964_: *mut crate::leanh::LeanObject,
    mut v_l_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3966_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_3965_);
    return v___x_3966_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(
    mut v_00_u03b1_3967_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3968_: *mut crate::leanh::LeanObject,
    mut v_inst_3969_: *mut crate::leanh::LeanObject,
    mut v_l_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3971_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(
        v_00_u03b1_3967_,
        v_00_u03b2_3968_,
        v_inst_3969_,
        v_l_3970_,
    );
    crate::leanh::lean_dec_ref(v_inst_3969_);
    return v_res_3971_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_reverse___redArg(
    mut v_x_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3980_: u8 = 0;
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3972_) == 0 {
                    v_size_3973_ = crate::leanh::lean_ctor_get(v_x_3972_, 0);
                    v_k_3974_ = crate::leanh::lean_ctor_get(v_x_3972_, 1);
                    v_v_3975_ = crate::leanh::lean_ctor_get(v_x_3972_, 2);
                    v_l_3976_ = crate::leanh::lean_ctor_get(v_x_3972_, 3);
                    v_r_3977_ = crate::leanh::lean_ctor_get(v_x_3972_, 4);
                    v_isSharedCheck_3986_ = (!crate::leanh::lean_is_exclusive(v_x_3972_)) as u8;
                    if v_isSharedCheck_3986_ == 0 {
                        v___x_3979_ = v_x_3972_;
                        v_isShared_3980_ = v_isSharedCheck_3986_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_3977_);
                        crate::leanh::lean_inc(v_l_3976_);
                        crate::leanh::lean_inc(v_v_3975_);
                        crate::leanh::lean_inc(v_k_3974_);
                        crate::leanh::lean_inc(v_size_3973_);
                        crate::leanh::lean_dec(v_x_3972_);
                        v___x_3979_ = crate::leanh::lean_box(0);
                        v_isShared_3980_ = v_isSharedCheck_3986_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_3972_;
                }
            }
            1 => {
                v___x_3981_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_r_3977_);
                v___x_3982_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_l_3976_);
                if v_isShared_3980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3979_, 4, v___x_3982_);
                    crate::leanh::lean_ctor_set(v___x_3979_, 3, v___x_3981_);
                    v___x_3984_ = v___x_3979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_size_3973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_k_3974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 2, v_v_3975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 3, v___x_3981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 4, v___x_3982_);
                    v___x_3984_ = v_reuseFailAlloc_3985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_reverse(
    mut v_00_u03b1_3987_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3988_: *mut crate::leanh::LeanObject,
    mut v_x_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_3989_);
    return v___x_3990_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(
    mut v_c_3991_: *mut crate::leanh::LeanObject,
    mut v_x_3992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3993_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_3991_);
    return v___x_3993_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
    mut v_inst_3995_: *mut crate::leanh::LeanObject,
    mut v_l_3996_: *mut crate::leanh::LeanObject,
    mut v_k_3997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3998_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0;
    v___x_3999_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
        v_inst_3995_,
        v_k_3997_,
        v_l_3996_,
        v___f_3998_,
    );
    return v___x_3999_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098(
    mut v_00_u03b1_4000_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4001_: *mut crate::leanh::LeanObject,
    mut v_inst_4002_: *mut crate::leanh::LeanObject,
    mut v_l_4003_: *mut crate::leanh::LeanObject,
    mut v_k_4004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4005_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
        v_inst_4002_,
        v_l_4003_,
        v_k_4004_,
    );
    return v___x_4005_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(
    mut v_inst_4006_: *mut crate::leanh::LeanObject,
    mut v_l_4007_: *mut crate::leanh::LeanObject,
    mut v_k_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4009_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
        v_inst_4006_,
        v_l_4007_,
        v_k_4008_,
    );
    v_val_4010_ = crate::leanh::lean_ctor_get(v___x_4009_, 0);
    crate::leanh::lean_inc(v_val_4010_);
    crate::leanh::lean_dec(v___x_4009_);
    return v_val_4010_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_u2098(
    mut v_00_u03b1_4011_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4012_: *mut crate::leanh::LeanObject,
    mut v_inst_4013_: *mut crate::leanh::LeanObject,
    mut v_l_4014_: *mut crate::leanh::LeanObject,
    mut v_k_4015_: *mut crate::leanh::LeanObject,
    mut v_h_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4017_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_4013_, v_l_4014_, v_k_4015_);
    return v___x_4017_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(
    mut v_inst_4018_: *mut crate::leanh::LeanObject,
    mut v_l_4019_: *mut crate::leanh::LeanObject,
    mut v_k_4020_: *mut crate::leanh::LeanObject,
    mut v_inst_4021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4022_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
        v_inst_4018_,
        v_l_4019_,
        v_k_4020_,
    );
    if crate::leanh::lean_obj_tag(v___x_4022_) == 0 {
        let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4023_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3,
        );
        v___x_4024_ = l_panic___redArg(v_inst_4021_, v___x_4023_);
        return v___x_4024_;
    } else {
        let mut v_val_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4025_ = crate::leanh::lean_ctor_get(v___x_4022_, 0);
        crate::leanh::lean_inc(v_val_4025_);
        crate::leanh::lean_dec_ref_known(v___x_4022_, 1);
        return v_val_4025_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg___boxed(
    mut v_inst_4026_: *mut crate::leanh::LeanObject,
    mut v_l_4027_: *mut crate::leanh::LeanObject,
    mut v_k_4028_: *mut crate::leanh::LeanObject,
    mut v_inst_4029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4030_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(
        v_inst_4026_,
        v_l_4027_,
        v_k_4028_,
        v_inst_4029_,
    );
    crate::leanh::lean_dec(v_inst_4029_);
    return v_res_4030_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(
    mut v_00_u03b1_4031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4032_: *mut crate::leanh::LeanObject,
    mut v_inst_4033_: *mut crate::leanh::LeanObject,
    mut v_l_4034_: *mut crate::leanh::LeanObject,
    mut v_k_4035_: *mut crate::leanh::LeanObject,
    mut v_inst_4036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(
        v_inst_4033_,
        v_l_4034_,
        v_k_4035_,
        v_inst_4036_,
    );
    return v___x_4037_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___boxed(
    mut v_00_u03b1_4038_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4039_: *mut crate::leanh::LeanObject,
    mut v_inst_4040_: *mut crate::leanh::LeanObject,
    mut v_l_4041_: *mut crate::leanh::LeanObject,
    mut v_k_4042_: *mut crate::leanh::LeanObject,
    mut v_inst_4043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4044_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(
        v_00_u03b1_4038_,
        v_00_u03b2_4039_,
        v_inst_4040_,
        v_l_4041_,
        v_k_4042_,
        v_inst_4043_,
    );
    crate::leanh::lean_dec(v_inst_4043_);
    return v_res_4044_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(
    mut v_inst_4045_: *mut crate::leanh::LeanObject,
    mut v_l_4046_: *mut crate::leanh::LeanObject,
    mut v_k_4047_: *mut crate::leanh::LeanObject,
    mut v_fallback_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4049_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
        v_inst_4045_,
        v_l_4046_,
        v_k_4047_,
    );
    if crate::leanh::lean_obj_tag(v___x_4049_) == 0 {
        crate::leanh::lean_inc(v_fallback_4048_);
        return v_fallback_4048_;
    } else {
        let mut v_val_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4050_ = crate::leanh::lean_ctor_get(v___x_4049_, 0);
        crate::leanh::lean_inc(v_val_4050_);
        crate::leanh::lean_dec_ref_known(v___x_4049_, 1);
        return v_val_4050_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(
    mut v_inst_4051_: *mut crate::leanh::LeanObject,
    mut v_l_4052_: *mut crate::leanh::LeanObject,
    mut v_k_4053_: *mut crate::leanh::LeanObject,
    mut v_fallback_4054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4055_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(
        v_inst_4051_,
        v_l_4052_,
        v_k_4053_,
        v_fallback_4054_,
    );
    crate::leanh::lean_dec(v_fallback_4054_);
    return v_res_4055_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(
    mut v_00_u03b1_4056_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4057_: *mut crate::leanh::LeanObject,
    mut v_inst_4058_: *mut crate::leanh::LeanObject,
    mut v_l_4059_: *mut crate::leanh::LeanObject,
    mut v_k_4060_: *mut crate::leanh::LeanObject,
    mut v_fallback_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4062_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(
        v_inst_4058_,
        v_l_4059_,
        v_k_4060_,
        v_fallback_4061_,
    );
    return v___x_4062_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(
    mut v_00_u03b1_4063_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4064_: *mut crate::leanh::LeanObject,
    mut v_inst_4065_: *mut crate::leanh::LeanObject,
    mut v_l_4066_: *mut crate::leanh::LeanObject,
    mut v_k_4067_: *mut crate::leanh::LeanObject,
    mut v_fallback_4068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4069_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(
        v_00_u03b1_4063_,
        v_00_u03b2_4064_,
        v_inst_4065_,
        v_l_4066_,
        v_k_4067_,
        v_fallback_4068_,
    );
    crate::leanh::lean_dec(v_fallback_4068_);
    return v_res_4069_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(
    mut v_t_4070_: *mut crate::leanh::LeanObject,
    mut v_h__1_4071_: *mut crate::leanh::LeanObject,
    mut v_h__2_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4070_) == 0 {
        let mut v_size_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4071_);
        v_size_4073_ = crate::leanh::lean_ctor_get(v_t_4070_, 0);
        crate::leanh::lean_inc(v_size_4073_);
        v_k_4074_ = crate::leanh::lean_ctor_get(v_t_4070_, 1);
        crate::leanh::lean_inc(v_k_4074_);
        v_v_4075_ = crate::leanh::lean_ctor_get(v_t_4070_, 2);
        crate::leanh::lean_inc(v_v_4075_);
        v_l_4076_ = crate::leanh::lean_ctor_get(v_t_4070_, 3);
        crate::leanh::lean_inc(v_l_4076_);
        v_r_4077_ = crate::leanh::lean_ctor_get(v_t_4070_, 4);
        crate::leanh::lean_inc(v_r_4077_);
        crate::leanh::lean_dec_ref_known(v_t_4070_, 5);
        v___x_4078_ = crate::leanh::lean_apply_5(
            v_h__2_4072_,
            v_size_4073_,
            v_k_4074_,
            v_v_4075_,
            v_l_4076_,
            v_r_4077_,
        );
        return v___x_4078_;
    } else {
        let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4072_);
        v___x_4079_ = crate::leanh::lean_box(0);
        v___x_4080_ = crate::leanh::lean_apply_1(v_h__1_4071_, v___x_4079_);
        return v___x_4080_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(
    mut v_00_u03b1_4081_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4082_: *mut crate::leanh::LeanObject,
    mut v_motive_4083_: *mut crate::leanh::LeanObject,
    mut v_t_4084_: *mut crate::leanh::LeanObject,
    mut v_h__1_4085_: *mut crate::leanh::LeanObject,
    mut v_h__2_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4084_) == 0 {
        let mut v_size_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4085_);
        v_size_4087_ = crate::leanh::lean_ctor_get(v_t_4084_, 0);
        crate::leanh::lean_inc(v_size_4087_);
        v_k_4088_ = crate::leanh::lean_ctor_get(v_t_4084_, 1);
        crate::leanh::lean_inc(v_k_4088_);
        v_v_4089_ = crate::leanh::lean_ctor_get(v_t_4084_, 2);
        crate::leanh::lean_inc(v_v_4089_);
        v_l_4090_ = crate::leanh::lean_ctor_get(v_t_4084_, 3);
        crate::leanh::lean_inc(v_l_4090_);
        v_r_4091_ = crate::leanh::lean_ctor_get(v_t_4084_, 4);
        crate::leanh::lean_inc(v_r_4091_);
        crate::leanh::lean_dec_ref_known(v_t_4084_, 5);
        v___x_4092_ = crate::leanh::lean_apply_5(
            v_h__2_4086_,
            v_size_4087_,
            v_k_4088_,
            v_v_4089_,
            v_l_4090_,
            v_r_4091_,
        );
        return v___x_4092_;
    } else {
        let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4086_);
        v___x_4093_ = crate::leanh::lean_box(0);
        v___x_4094_ = crate::leanh::lean_apply_1(v_h__1_4085_, v___x_4093_);
        return v___x_4094_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(
    mut v_x_4095_: u8,
    mut v_h__1_4096_: *mut crate::leanh::LeanObject,
    mut v_h__2_4097_: *mut crate::leanh::LeanObject,
    mut v_h__3_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_4095_ {
        0 => {
            let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4098_);
            crate::leanh::lean_dec(v_h__2_4097_);
            v___x_4099_ = crate::leanh::lean_apply_1(v_h__1_4096_, crate::leanh::lean_box(0));
            return v___x_4099_;
        }
        1 => {
            let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4097_);
            crate::leanh::lean_dec(v_h__1_4096_);
            v___x_4100_ = crate::leanh::lean_apply_1(v_h__3_4098_, crate::leanh::lean_box(0));
            return v___x_4100_;
        }
        _ => {
            let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4098_);
            crate::leanh::lean_dec(v_h__1_4096_);
            v___x_4101_ = crate::leanh::lean_apply_1(v_h__2_4097_, crate::leanh::lean_box(0));
            return v___x_4101_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(
    mut v_x_4102_: *mut crate::leanh::LeanObject,
    mut v_h__1_4103_: *mut crate::leanh::LeanObject,
    mut v_h__2_4104_: *mut crate::leanh::LeanObject,
    mut v_h__3_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_4106_: u8 = 0;
    let mut v_res_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_4106_ = (crate::leanh::lean_unbox(v_x_4102_) as u8);
    v_res_4107_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_33__boxed_4106_, v_h__1_4103_, v_h__2_4104_, v_h__3_4105_);
    return v_res_4107_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(
    mut v_motive_4108_: *mut crate::leanh::LeanObject,
    mut v_x_4109_: u8,
    mut v_h__1_4110_: *mut crate::leanh::LeanObject,
    mut v_h__2_4111_: *mut crate::leanh::LeanObject,
    mut v_h__3_4112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_4109_ {
        0 => {
            let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4112_);
            crate::leanh::lean_dec(v_h__2_4111_);
            v___x_4113_ = crate::leanh::lean_apply_1(v_h__1_4110_, crate::leanh::lean_box(0));
            return v___x_4113_;
        }
        1 => {
            let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4111_);
            crate::leanh::lean_dec(v_h__1_4110_);
            v___x_4114_ = crate::leanh::lean_apply_1(v_h__3_4112_, crate::leanh::lean_box(0));
            return v___x_4114_;
        }
        _ => {
            let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4112_);
            crate::leanh::lean_dec(v_h__1_4110_);
            v___x_4115_ = crate::leanh::lean_apply_1(v_h__2_4111_, crate::leanh::lean_box(0));
            return v___x_4115_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(
    mut v_motive_4116_: *mut crate::leanh::LeanObject,
    mut v_x_4117_: *mut crate::leanh::LeanObject,
    mut v_h__1_4118_: *mut crate::leanh::LeanObject,
    mut v_h__2_4119_: *mut crate::leanh::LeanObject,
    mut v_h__3_4120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42__boxed_4121_: u8 = 0;
    let mut v_res_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_4121_ = (crate::leanh::lean_unbox(v_x_4117_) as u8);
    v_res_4122_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_4116_, v_x_42__boxed_4121_, v_h__1_4118_, v_h__2_4119_, v_h__3_4120_);
    return v_res_4122_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(
    mut v_x_4123_: *mut crate::leanh::LeanObject,
    mut v_h__1_4124_: *mut crate::leanh::LeanObject,
    mut v_h__2_4125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4123_) == 0 {
        let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4125_);
        v___x_4126_ = crate::leanh::lean_apply_1(v_h__1_4124_, crate::leanh::lean_box(0));
        return v___x_4126_;
    } else {
        let mut v_val_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4124_);
        v_val_4127_ = crate::leanh::lean_ctor_get(v_x_4123_, 0);
        crate::leanh::lean_inc(v_val_4127_);
        crate::leanh::lean_dec_ref_known(v_x_4123_, 1);
        v___x_4128_ =
            crate::leanh::lean_apply_2(v_h__2_4125_, v_val_4127_, crate::leanh::lean_box(0));
        return v___x_4128_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(
    mut v_00_u03b1_4129_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4130_: *mut crate::leanh::LeanObject,
    mut v_motive_4131_: *mut crate::leanh::LeanObject,
    mut v_x_4132_: *mut crate::leanh::LeanObject,
    mut v_h__1_4133_: *mut crate::leanh::LeanObject,
    mut v_h__2_4134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4132_) == 0 {
        let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4134_);
        v___x_4135_ = crate::leanh::lean_apply_1(v_h__1_4133_, crate::leanh::lean_box(0));
        return v___x_4135_;
    } else {
        let mut v_val_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4133_);
        v_val_4136_ = crate::leanh::lean_ctor_get(v_x_4132_, 0);
        crate::leanh::lean_inc(v_val_4136_);
        crate::leanh::lean_dec_ref_known(v_x_4132_, 1);
        v___x_4137_ =
            crate::leanh::lean_apply_2(v_h__2_4134_, v_val_4136_, crate::leanh::lean_box(0));
        return v___x_4137_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(
    mut v_t_4138_: *mut crate::leanh::LeanObject,
    mut v_h__1_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_4140_ = crate::leanh::lean_ctor_get(v_t_4138_, 0);
    crate::leanh::lean_inc(v_size_4140_);
    v_k_4141_ = crate::leanh::lean_ctor_get(v_t_4138_, 1);
    crate::leanh::lean_inc(v_k_4141_);
    v_v_4142_ = crate::leanh::lean_ctor_get(v_t_4138_, 2);
    crate::leanh::lean_inc(v_v_4142_);
    v_l_4143_ = crate::leanh::lean_ctor_get(v_t_4138_, 3);
    crate::leanh::lean_inc(v_l_4143_);
    v_r_4144_ = crate::leanh::lean_ctor_get(v_t_4138_, 4);
    crate::leanh::lean_inc(v_r_4144_);
    crate::leanh::lean_dec(v_t_4138_);
    v___x_4145_ = crate::leanh::lean_apply_6(
        v_h__1_4139_,
        v_size_4140_,
        v_k_4141_,
        v_v_4142_,
        v_l_4143_,
        v_r_4144_,
        crate::leanh::lean_box(0),
    );
    return v___x_4145_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(
    mut v_00_u03b1_4146_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4147_: *mut crate::leanh::LeanObject,
    mut v_inst_4148_: *mut crate::leanh::LeanObject,
    mut v_k_4149_: *mut crate::leanh::LeanObject,
    mut v_motive_4150_: *mut crate::leanh::LeanObject,
    mut v_t_4151_: *mut crate::leanh::LeanObject,
    mut v_hlk_4152_: *mut crate::leanh::LeanObject,
    mut v_h__1_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_4154_ = crate::leanh::lean_ctor_get(v_t_4151_, 0);
    crate::leanh::lean_inc(v_size_4154_);
    v_k_4155_ = crate::leanh::lean_ctor_get(v_t_4151_, 1);
    crate::leanh::lean_inc(v_k_4155_);
    v_v_4156_ = crate::leanh::lean_ctor_get(v_t_4151_, 2);
    crate::leanh::lean_inc(v_v_4156_);
    v_l_4157_ = crate::leanh::lean_ctor_get(v_t_4151_, 3);
    crate::leanh::lean_inc(v_l_4157_);
    v_r_4158_ = crate::leanh::lean_ctor_get(v_t_4151_, 4);
    crate::leanh::lean_inc(v_r_4158_);
    crate::leanh::lean_dec(v_t_4151_);
    v___x_4159_ = crate::leanh::lean_apply_6(
        v_h__1_4153_,
        v_size_4154_,
        v_k_4155_,
        v_v_4156_,
        v_l_4157_,
        v_r_4158_,
        crate::leanh::lean_box(0),
    );
    return v___x_4159_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(
    mut v_00_u03b1_4160_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4161_: *mut crate::leanh::LeanObject,
    mut v_inst_4162_: *mut crate::leanh::LeanObject,
    mut v_k_4163_: *mut crate::leanh::LeanObject,
    mut v_motive_4164_: *mut crate::leanh::LeanObject,
    mut v_t_4165_: *mut crate::leanh::LeanObject,
    mut v_hlk_4166_: *mut crate::leanh::LeanObject,
    mut v_h__1_4167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4168_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(v_00_u03b1_4160_, v_00_u03b2_4161_, v_inst_4162_, v_k_4163_, v_motive_4164_, v_t_4165_, v_hlk_4166_, v_h__1_4167_);
    crate::leanh::lean_dec(v_k_4163_);
    crate::leanh::lean_dec_ref(v_inst_4162_);
    return v_res_4168_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_4169_: *mut crate::leanh::LeanObject,
    mut v_h__1_4170_: *mut crate::leanh::LeanObject,
    mut v_h__2_4171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4169_) == 0 {
        let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4171_);
        v___x_4172_ = crate::leanh::lean_box(0);
        v___x_4173_ = crate::leanh::lean_apply_1(v_h__1_4170_, v___x_4172_);
        return v___x_4173_;
    } else {
        let mut v_val_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4170_);
        v_val_4174_ = crate::leanh::lean_ctor_get(v_x_4169_, 0);
        crate::leanh::lean_inc(v_val_4174_);
        crate::leanh::lean_dec_ref_known(v_x_4169_, 1);
        v___x_4175_ = crate::leanh::lean_apply_1(v_h__2_4171_, v_val_4174_);
        return v___x_4175_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4177_: *mut crate::leanh::LeanObject,
    mut v_motive_4178_: *mut crate::leanh::LeanObject,
    mut v_x_4179_: *mut crate::leanh::LeanObject,
    mut v_h__1_4180_: *mut crate::leanh::LeanObject,
    mut v_h__2_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4179_) == 0 {
        let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4181_);
        v___x_4182_ = crate::leanh::lean_box(0);
        v___x_4183_ = crate::leanh::lean_apply_1(v_h__1_4180_, v___x_4182_);
        return v___x_4183_;
    } else {
        let mut v_val_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4180_);
        v_val_4184_ = crate::leanh::lean_ctor_get(v_x_4179_, 0);
        crate::leanh::lean_inc(v_val_4184_);
        crate::leanh::lean_dec_ref_known(v_x_4179_, 1);
        v___x_4185_ = crate::leanh::lean_apply_1(v_h__2_4181_, v_val_4184_);
        return v___x_4185_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(
    mut v_t_4186_: *mut crate::leanh::LeanObject,
    mut v_h__1_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_4188_ = crate::leanh::lean_ctor_get(v_t_4186_, 0);
    crate::leanh::lean_inc(v_size_4188_);
    v_k_4189_ = crate::leanh::lean_ctor_get(v_t_4186_, 1);
    crate::leanh::lean_inc(v_k_4189_);
    v_v_4190_ = crate::leanh::lean_ctor_get(v_t_4186_, 2);
    crate::leanh::lean_inc(v_v_4190_);
    v_l_4191_ = crate::leanh::lean_ctor_get(v_t_4186_, 3);
    crate::leanh::lean_inc(v_l_4191_);
    v_r_4192_ = crate::leanh::lean_ctor_get(v_t_4186_, 4);
    crate::leanh::lean_inc(v_r_4192_);
    crate::leanh::lean_dec(v_t_4186_);
    v___x_4193_ = crate::leanh::lean_apply_6(
        v_h__1_4187_,
        v_size_4188_,
        v_k_4189_,
        v_v_4190_,
        v_l_4191_,
        v_r_4192_,
        crate::leanh::lean_box(0),
    );
    return v___x_4193_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(
    mut v_00_u03b1_4194_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4195_: *mut crate::leanh::LeanObject,
    mut v_inst_4196_: *mut crate::leanh::LeanObject,
    mut v_k_4197_: *mut crate::leanh::LeanObject,
    mut v_motive_4198_: *mut crate::leanh::LeanObject,
    mut v_t_4199_: *mut crate::leanh::LeanObject,
    mut v_hlk_4200_: *mut crate::leanh::LeanObject,
    mut v_h__1_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_4202_ = crate::leanh::lean_ctor_get(v_t_4199_, 0);
    crate::leanh::lean_inc(v_size_4202_);
    v_k_4203_ = crate::leanh::lean_ctor_get(v_t_4199_, 1);
    crate::leanh::lean_inc(v_k_4203_);
    v_v_4204_ = crate::leanh::lean_ctor_get(v_t_4199_, 2);
    crate::leanh::lean_inc(v_v_4204_);
    v_l_4205_ = crate::leanh::lean_ctor_get(v_t_4199_, 3);
    crate::leanh::lean_inc(v_l_4205_);
    v_r_4206_ = crate::leanh::lean_ctor_get(v_t_4199_, 4);
    crate::leanh::lean_inc(v_r_4206_);
    crate::leanh::lean_dec(v_t_4199_);
    v___x_4207_ = crate::leanh::lean_apply_6(
        v_h__1_4201_,
        v_size_4202_,
        v_k_4203_,
        v_v_4204_,
        v_l_4205_,
        v_r_4206_,
        crate::leanh::lean_box(0),
    );
    return v___x_4207_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(
    mut v_00_u03b1_4208_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4209_: *mut crate::leanh::LeanObject,
    mut v_inst_4210_: *mut crate::leanh::LeanObject,
    mut v_k_4211_: *mut crate::leanh::LeanObject,
    mut v_motive_4212_: *mut crate::leanh::LeanObject,
    mut v_t_4213_: *mut crate::leanh::LeanObject,
    mut v_hlk_4214_: *mut crate::leanh::LeanObject,
    mut v_h__1_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4216_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(v_00_u03b1_4208_, v_00_u03b2_4209_, v_inst_4210_, v_k_4211_, v_motive_4212_, v_t_4213_, v_hlk_4214_, v_h__1_4215_);
    crate::leanh::lean_dec(v_k_4211_);
    crate::leanh::lean_dec_ref(v_inst_4210_);
    return v_res_4216_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(
    mut v_x_4217_: *mut crate::leanh::LeanObject,
    mut v_h__1_4218_: *mut crate::leanh::LeanObject,
    mut v_h__2_4219_: *mut crate::leanh::LeanObject,
    mut v_h__3_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4217_) == 0 {
        let mut v_l_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4218_);
        v_l_4221_ = crate::leanh::lean_ctor_get(v_x_4217_, 3);
        if crate::leanh::lean_obj_tag(v_l_4221_) == 0 {
            let mut v_size_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4221_);
            crate::leanh::lean_dec(v_h__2_4219_);
            v_size_4222_ = crate::leanh::lean_ctor_get(v_x_4217_, 0);
            crate::leanh::lean_inc(v_size_4222_);
            v_k_4223_ = crate::leanh::lean_ctor_get(v_x_4217_, 1);
            crate::leanh::lean_inc(v_k_4223_);
            v_v_4224_ = crate::leanh::lean_ctor_get(v_x_4217_, 2);
            crate::leanh::lean_inc(v_v_4224_);
            v_r_4225_ = crate::leanh::lean_ctor_get(v_x_4217_, 4);
            crate::leanh::lean_inc(v_r_4225_);
            crate::leanh::lean_dec_ref_known(v_x_4217_, 5);
            v_size_4226_ = crate::leanh::lean_ctor_get(v_l_4221_, 0);
            crate::leanh::lean_inc(v_size_4226_);
            v_k_4227_ = crate::leanh::lean_ctor_get(v_l_4221_, 1);
            crate::leanh::lean_inc(v_k_4227_);
            v_v_4228_ = crate::leanh::lean_ctor_get(v_l_4221_, 2);
            crate::leanh::lean_inc(v_v_4228_);
            v_l_4229_ = crate::leanh::lean_ctor_get(v_l_4221_, 3);
            crate::leanh::lean_inc(v_l_4229_);
            v_r_4230_ = crate::leanh::lean_ctor_get(v_l_4221_, 4);
            crate::leanh::lean_inc(v_r_4230_);
            crate::leanh::lean_dec_ref_known(v_l_4221_, 5);
            v___x_4231_ = crate::leanh::lean_apply_9(
                v_h__3_4220_,
                v_size_4222_,
                v_k_4223_,
                v_v_4224_,
                v_size_4226_,
                v_k_4227_,
                v_v_4228_,
                v_l_4229_,
                v_r_4230_,
                v_r_4225_,
            );
            return v___x_4231_;
        } else {
            let mut v_size_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4220_);
            v_size_4232_ = crate::leanh::lean_ctor_get(v_x_4217_, 0);
            crate::leanh::lean_inc(v_size_4232_);
            v_k_4233_ = crate::leanh::lean_ctor_get(v_x_4217_, 1);
            crate::leanh::lean_inc(v_k_4233_);
            v_v_4234_ = crate::leanh::lean_ctor_get(v_x_4217_, 2);
            crate::leanh::lean_inc(v_v_4234_);
            v_r_4235_ = crate::leanh::lean_ctor_get(v_x_4217_, 4);
            crate::leanh::lean_inc(v_r_4235_);
            crate::leanh::lean_dec_ref_known(v_x_4217_, 5);
            v___x_4236_ = crate::leanh::lean_apply_4(
                v_h__2_4219_,
                v_size_4232_,
                v_k_4233_,
                v_v_4234_,
                v_r_4235_,
            );
            return v___x_4236_;
        }
    } else {
        let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4220_);
        crate::leanh::lean_dec(v_h__2_4219_);
        v___x_4237_ = crate::leanh::lean_box(0);
        v___x_4238_ = crate::leanh::lean_apply_1(v_h__1_4218_, v___x_4237_);
        return v___x_4238_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4239_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4240_: *mut crate::leanh::LeanObject,
    mut v_motive_4241_: *mut crate::leanh::LeanObject,
    mut v_x_4242_: *mut crate::leanh::LeanObject,
    mut v_h__1_4243_: *mut crate::leanh::LeanObject,
    mut v_h__2_4244_: *mut crate::leanh::LeanObject,
    mut v_h__3_4245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4242_) == 0 {
        let mut v_l_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4243_);
        v_l_4246_ = crate::leanh::lean_ctor_get(v_x_4242_, 3);
        if crate::leanh::lean_obj_tag(v_l_4246_) == 0 {
            let mut v_size_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4246_);
            crate::leanh::lean_dec(v_h__2_4244_);
            v_size_4247_ = crate::leanh::lean_ctor_get(v_x_4242_, 0);
            crate::leanh::lean_inc(v_size_4247_);
            v_k_4248_ = crate::leanh::lean_ctor_get(v_x_4242_, 1);
            crate::leanh::lean_inc(v_k_4248_);
            v_v_4249_ = crate::leanh::lean_ctor_get(v_x_4242_, 2);
            crate::leanh::lean_inc(v_v_4249_);
            v_r_4250_ = crate::leanh::lean_ctor_get(v_x_4242_, 4);
            crate::leanh::lean_inc(v_r_4250_);
            crate::leanh::lean_dec_ref_known(v_x_4242_, 5);
            v_size_4251_ = crate::leanh::lean_ctor_get(v_l_4246_, 0);
            crate::leanh::lean_inc(v_size_4251_);
            v_k_4252_ = crate::leanh::lean_ctor_get(v_l_4246_, 1);
            crate::leanh::lean_inc(v_k_4252_);
            v_v_4253_ = crate::leanh::lean_ctor_get(v_l_4246_, 2);
            crate::leanh::lean_inc(v_v_4253_);
            v_l_4254_ = crate::leanh::lean_ctor_get(v_l_4246_, 3);
            crate::leanh::lean_inc(v_l_4254_);
            v_r_4255_ = crate::leanh::lean_ctor_get(v_l_4246_, 4);
            crate::leanh::lean_inc(v_r_4255_);
            crate::leanh::lean_dec_ref_known(v_l_4246_, 5);
            v___x_4256_ = crate::leanh::lean_apply_9(
                v_h__3_4245_,
                v_size_4247_,
                v_k_4248_,
                v_v_4249_,
                v_size_4251_,
                v_k_4252_,
                v_v_4253_,
                v_l_4254_,
                v_r_4255_,
                v_r_4250_,
            );
            return v___x_4256_;
        } else {
            let mut v_size_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4245_);
            v_size_4257_ = crate::leanh::lean_ctor_get(v_x_4242_, 0);
            crate::leanh::lean_inc(v_size_4257_);
            v_k_4258_ = crate::leanh::lean_ctor_get(v_x_4242_, 1);
            crate::leanh::lean_inc(v_k_4258_);
            v_v_4259_ = crate::leanh::lean_ctor_get(v_x_4242_, 2);
            crate::leanh::lean_inc(v_v_4259_);
            v_r_4260_ = crate::leanh::lean_ctor_get(v_x_4242_, 4);
            crate::leanh::lean_inc(v_r_4260_);
            crate::leanh::lean_dec_ref_known(v_x_4242_, 5);
            v___x_4261_ = crate::leanh::lean_apply_4(
                v_h__2_4244_,
                v_size_4257_,
                v_k_4258_,
                v_v_4259_,
                v_r_4260_,
            );
            return v___x_4261_;
        }
    } else {
        let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4245_);
        crate::leanh::lean_dec(v_h__2_4244_);
        v___x_4262_ = crate::leanh::lean_box(0);
        v___x_4263_ = crate::leanh::lean_apply_1(v_h__1_4243_, v___x_4262_);
        return v___x_4263_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(
    mut v_step_4264_: *mut crate::leanh::LeanObject,
    mut v_h__1_4265_: *mut crate::leanh::LeanObject,
    mut v_h__2_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_step_4264_) == 0 {
        let mut v_a_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4266_);
        v_a_4267_ = crate::leanh::lean_ctor_get(v_step_4264_, 0);
        crate::leanh::lean_inc(v_a_4267_);
        v_a_4268_ = crate::leanh::lean_ctor_get(v_step_4264_, 1);
        crate::leanh::lean_inc(v_a_4268_);
        v_a_4269_ = crate::leanh::lean_ctor_get(v_step_4264_, 2);
        crate::leanh::lean_inc(v_a_4269_);
        crate::leanh::lean_dec_ref_known(v_step_4264_, 3);
        v___x_4270_ = crate::leanh::lean_apply_4(
            v_h__1_4265_,
            v_a_4267_,
            crate::leanh::lean_box(0),
            v_a_4268_,
            v_a_4269_,
        );
        return v___x_4270_;
    } else {
        let mut v_a_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4265_);
        v_a_4271_ = crate::leanh::lean_ctor_get(v_step_4264_, 0);
        crate::leanh::lean_inc(v_a_4271_);
        v_a_4272_ = crate::leanh::lean_ctor_get(v_step_4264_, 1);
        crate::leanh::lean_inc(v_a_4272_);
        v_a_4273_ = crate::leanh::lean_ctor_get(v_step_4264_, 2);
        crate::leanh::lean_inc(v_a_4273_);
        crate::leanh::lean_dec_ref_known(v_step_4264_, 3);
        v___x_4274_ = crate::leanh::lean_apply_3(v_h__2_4266_, v_a_4271_, v_a_4272_, v_a_4273_);
        return v___x_4274_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(
    mut v_00_u03b1_4275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4276_: *mut crate::leanh::LeanObject,
    mut v_inst_4277_: *mut crate::leanh::LeanObject,
    mut v_motive_4278_: *mut crate::leanh::LeanObject,
    mut v_step_4279_: *mut crate::leanh::LeanObject,
    mut v_h__1_4280_: *mut crate::leanh::LeanObject,
    mut v_h__2_4281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_step_4279_) == 0 {
        let mut v_a_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4281_);
        v_a_4282_ = crate::leanh::lean_ctor_get(v_step_4279_, 0);
        crate::leanh::lean_inc(v_a_4282_);
        v_a_4283_ = crate::leanh::lean_ctor_get(v_step_4279_, 1);
        crate::leanh::lean_inc(v_a_4283_);
        v_a_4284_ = crate::leanh::lean_ctor_get(v_step_4279_, 2);
        crate::leanh::lean_inc(v_a_4284_);
        crate::leanh::lean_dec_ref_known(v_step_4279_, 3);
        v___x_4285_ = crate::leanh::lean_apply_4(
            v_h__1_4280_,
            v_a_4282_,
            crate::leanh::lean_box(0),
            v_a_4283_,
            v_a_4284_,
        );
        return v___x_4285_;
    } else {
        let mut v_a_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4280_);
        v_a_4286_ = crate::leanh::lean_ctor_get(v_step_4279_, 0);
        crate::leanh::lean_inc(v_a_4286_);
        v_a_4287_ = crate::leanh::lean_ctor_get(v_step_4279_, 1);
        crate::leanh::lean_inc(v_a_4287_);
        v_a_4288_ = crate::leanh::lean_ctor_get(v_step_4279_, 2);
        crate::leanh::lean_inc(v_a_4288_);
        crate::leanh::lean_dec_ref_known(v_step_4279_, 3);
        v___x_4289_ = crate::leanh::lean_apply_3(v_h__2_4281_, v_a_4286_, v_a_4287_, v_a_4288_);
        return v___x_4289_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(
    mut v_00_u03b1_4290_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4291_: *mut crate::leanh::LeanObject,
    mut v_inst_4292_: *mut crate::leanh::LeanObject,
    mut v_motive_4293_: *mut crate::leanh::LeanObject,
    mut v_step_4294_: *mut crate::leanh::LeanObject,
    mut v_h__1_4295_: *mut crate::leanh::LeanObject,
    mut v_h__2_4296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4297_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_4290_, v_00_u03b2_4291_, v_inst_4292_, v_motive_4293_, v_step_4294_, v_h__1_4295_, v_h__2_4296_);
    crate::leanh::lean_dec_ref(v_inst_4292_);
    return v_res_4297_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(
    mut v_x_4298_: *mut crate::leanh::LeanObject,
    mut v_x_4299_: *mut crate::leanh::LeanObject,
    mut v_h__1_4300_: *mut crate::leanh::LeanObject,
    mut v_h__2_4301_: *mut crate::leanh::LeanObject,
    mut v_h__3_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4298_) == 0 {
        let mut v_l_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4300_);
        v_l_4303_ = crate::leanh::lean_ctor_get(v_x_4298_, 3);
        if crate::leanh::lean_obj_tag(v_l_4303_) == 0 {
            let mut v_size_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4303_);
            crate::leanh::lean_dec(v_h__2_4301_);
            v_size_4304_ = crate::leanh::lean_ctor_get(v_x_4298_, 0);
            crate::leanh::lean_inc(v_size_4304_);
            v_k_4305_ = crate::leanh::lean_ctor_get(v_x_4298_, 1);
            crate::leanh::lean_inc(v_k_4305_);
            v_v_4306_ = crate::leanh::lean_ctor_get(v_x_4298_, 2);
            crate::leanh::lean_inc(v_v_4306_);
            v_r_4307_ = crate::leanh::lean_ctor_get(v_x_4298_, 4);
            crate::leanh::lean_inc(v_r_4307_);
            crate::leanh::lean_dec_ref_known(v_x_4298_, 5);
            v_size_4308_ = crate::leanh::lean_ctor_get(v_l_4303_, 0);
            crate::leanh::lean_inc(v_size_4308_);
            v_k_4309_ = crate::leanh::lean_ctor_get(v_l_4303_, 1);
            crate::leanh::lean_inc(v_k_4309_);
            v_v_4310_ = crate::leanh::lean_ctor_get(v_l_4303_, 2);
            crate::leanh::lean_inc(v_v_4310_);
            v_l_4311_ = crate::leanh::lean_ctor_get(v_l_4303_, 3);
            crate::leanh::lean_inc(v_l_4311_);
            v_r_4312_ = crate::leanh::lean_ctor_get(v_l_4303_, 4);
            crate::leanh::lean_inc(v_r_4312_);
            crate::leanh::lean_dec_ref_known(v_l_4303_, 5);
            v___x_4313_ = crate::leanh::lean_apply_10(
                v_h__3_4302_,
                v_size_4304_,
                v_k_4305_,
                v_v_4306_,
                v_size_4308_,
                v_k_4309_,
                v_v_4310_,
                v_l_4311_,
                v_r_4312_,
                v_r_4307_,
                v_x_4299_,
            );
            return v___x_4313_;
        } else {
            let mut v_size_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4302_);
            v_size_4314_ = crate::leanh::lean_ctor_get(v_x_4298_, 0);
            crate::leanh::lean_inc(v_size_4314_);
            v_k_4315_ = crate::leanh::lean_ctor_get(v_x_4298_, 1);
            crate::leanh::lean_inc(v_k_4315_);
            v_v_4316_ = crate::leanh::lean_ctor_get(v_x_4298_, 2);
            crate::leanh::lean_inc(v_v_4316_);
            v_r_4317_ = crate::leanh::lean_ctor_get(v_x_4298_, 4);
            crate::leanh::lean_inc(v_r_4317_);
            crate::leanh::lean_dec_ref_known(v_x_4298_, 5);
            v___x_4318_ = crate::leanh::lean_apply_5(
                v_h__2_4301_,
                v_size_4314_,
                v_k_4315_,
                v_v_4316_,
                v_r_4317_,
                v_x_4299_,
            );
            return v___x_4318_;
        }
    } else {
        let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4302_);
        crate::leanh::lean_dec(v_h__2_4301_);
        v___x_4319_ = crate::leanh::lean_apply_1(v_h__1_4300_, v_x_4299_);
        return v___x_4319_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(
    mut v_00_u03b1_4320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4321_: *mut crate::leanh::LeanObject,
    mut v_motive_4322_: *mut crate::leanh::LeanObject,
    mut v_x_4323_: *mut crate::leanh::LeanObject,
    mut v_x_4324_: *mut crate::leanh::LeanObject,
    mut v_h__1_4325_: *mut crate::leanh::LeanObject,
    mut v_h__2_4326_: *mut crate::leanh::LeanObject,
    mut v_h__3_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4323_) == 0 {
        let mut v_l_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4325_);
        v_l_4328_ = crate::leanh::lean_ctor_get(v_x_4323_, 3);
        if crate::leanh::lean_obj_tag(v_l_4328_) == 0 {
            let mut v_size_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4328_);
            crate::leanh::lean_dec(v_h__2_4326_);
            v_size_4329_ = crate::leanh::lean_ctor_get(v_x_4323_, 0);
            crate::leanh::lean_inc(v_size_4329_);
            v_k_4330_ = crate::leanh::lean_ctor_get(v_x_4323_, 1);
            crate::leanh::lean_inc(v_k_4330_);
            v_v_4331_ = crate::leanh::lean_ctor_get(v_x_4323_, 2);
            crate::leanh::lean_inc(v_v_4331_);
            v_r_4332_ = crate::leanh::lean_ctor_get(v_x_4323_, 4);
            crate::leanh::lean_inc(v_r_4332_);
            crate::leanh::lean_dec_ref_known(v_x_4323_, 5);
            v_size_4333_ = crate::leanh::lean_ctor_get(v_l_4328_, 0);
            crate::leanh::lean_inc(v_size_4333_);
            v_k_4334_ = crate::leanh::lean_ctor_get(v_l_4328_, 1);
            crate::leanh::lean_inc(v_k_4334_);
            v_v_4335_ = crate::leanh::lean_ctor_get(v_l_4328_, 2);
            crate::leanh::lean_inc(v_v_4335_);
            v_l_4336_ = crate::leanh::lean_ctor_get(v_l_4328_, 3);
            crate::leanh::lean_inc(v_l_4336_);
            v_r_4337_ = crate::leanh::lean_ctor_get(v_l_4328_, 4);
            crate::leanh::lean_inc(v_r_4337_);
            crate::leanh::lean_dec_ref_known(v_l_4328_, 5);
            v___x_4338_ = crate::leanh::lean_apply_10(
                v_h__3_4327_,
                v_size_4329_,
                v_k_4330_,
                v_v_4331_,
                v_size_4333_,
                v_k_4334_,
                v_v_4335_,
                v_l_4336_,
                v_r_4337_,
                v_r_4332_,
                v_x_4324_,
            );
            return v___x_4338_;
        } else {
            let mut v_size_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4327_);
            v_size_4339_ = crate::leanh::lean_ctor_get(v_x_4323_, 0);
            crate::leanh::lean_inc(v_size_4339_);
            v_k_4340_ = crate::leanh::lean_ctor_get(v_x_4323_, 1);
            crate::leanh::lean_inc(v_k_4340_);
            v_v_4341_ = crate::leanh::lean_ctor_get(v_x_4323_, 2);
            crate::leanh::lean_inc(v_v_4341_);
            v_r_4342_ = crate::leanh::lean_ctor_get(v_x_4323_, 4);
            crate::leanh::lean_inc(v_r_4342_);
            crate::leanh::lean_dec_ref_known(v_x_4323_, 5);
            v___x_4343_ = crate::leanh::lean_apply_5(
                v_h__2_4326_,
                v_size_4339_,
                v_k_4340_,
                v_v_4341_,
                v_r_4342_,
                v_x_4324_,
            );
            return v___x_4343_;
        }
    } else {
        let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4327_);
        crate::leanh::lean_dec(v_h__2_4326_);
        v___x_4344_ = crate::leanh::lean_apply_1(v_h__1_4325_, v_x_4324_);
        return v___x_4344_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(
    mut v_x_4345_: *mut crate::leanh::LeanObject,
    mut v_h__1_4346_: *mut crate::leanh::LeanObject,
    mut v_h__2_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_4348_ = crate::leanh::lean_ctor_get(v_x_4345_, 3);
    if crate::leanh::lean_obj_tag(v_l_4348_) == 0 {
        let mut v_size_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_l_4348_);
        crate::leanh::lean_dec(v_h__1_4346_);
        v_size_4349_ = crate::leanh::lean_ctor_get(v_x_4345_, 0);
        crate::leanh::lean_inc(v_size_4349_);
        v_k_4350_ = crate::leanh::lean_ctor_get(v_x_4345_, 1);
        crate::leanh::lean_inc(v_k_4350_);
        v_v_4351_ = crate::leanh::lean_ctor_get(v_x_4345_, 2);
        crate::leanh::lean_inc(v_v_4351_);
        v_r_4352_ = crate::leanh::lean_ctor_get(v_x_4345_, 4);
        crate::leanh::lean_inc(v_r_4352_);
        crate::leanh::lean_dec(v_x_4345_);
        v_size_4353_ = crate::leanh::lean_ctor_get(v_l_4348_, 0);
        crate::leanh::lean_inc(v_size_4353_);
        v_k_4354_ = crate::leanh::lean_ctor_get(v_l_4348_, 1);
        crate::leanh::lean_inc(v_k_4354_);
        v_v_4355_ = crate::leanh::lean_ctor_get(v_l_4348_, 2);
        crate::leanh::lean_inc(v_v_4355_);
        v_l_4356_ = crate::leanh::lean_ctor_get(v_l_4348_, 3);
        crate::leanh::lean_inc(v_l_4356_);
        v_r_4357_ = crate::leanh::lean_ctor_get(v_l_4348_, 4);
        crate::leanh::lean_inc(v_r_4357_);
        crate::leanh::lean_dec_ref_known(v_l_4348_, 5);
        v___x_4358_ = crate::leanh::lean_apply_10(
            v_h__2_4347_,
            v_size_4349_,
            v_k_4350_,
            v_v_4351_,
            v_size_4353_,
            v_k_4354_,
            v_v_4355_,
            v_l_4356_,
            v_r_4357_,
            v_r_4352_,
            crate::leanh::lean_box(0),
        );
        return v___x_4358_;
    } else {
        let mut v_size_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4347_);
        v_size_4359_ = crate::leanh::lean_ctor_get(v_x_4345_, 0);
        crate::leanh::lean_inc(v_size_4359_);
        v_k_4360_ = crate::leanh::lean_ctor_get(v_x_4345_, 1);
        crate::leanh::lean_inc(v_k_4360_);
        v_v_4361_ = crate::leanh::lean_ctor_get(v_x_4345_, 2);
        crate::leanh::lean_inc(v_v_4361_);
        v_r_4362_ = crate::leanh::lean_ctor_get(v_x_4345_, 4);
        crate::leanh::lean_inc(v_r_4362_);
        crate::leanh::lean_dec(v_x_4345_);
        v___x_4363_ = crate::leanh::lean_apply_5(
            v_h__1_4346_,
            v_size_4359_,
            v_k_4360_,
            v_v_4361_,
            v_r_4362_,
            crate::leanh::lean_box(0),
        );
        return v___x_4363_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(
    mut v_00_u03b1_4364_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4365_: *mut crate::leanh::LeanObject,
    mut v_motive_4366_: *mut crate::leanh::LeanObject,
    mut v_x_4367_: *mut crate::leanh::LeanObject,
    mut v_x_4368_: *mut crate::leanh::LeanObject,
    mut v_h__1_4369_: *mut crate::leanh::LeanObject,
    mut v_h__2_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_4371_ = crate::leanh::lean_ctor_get(v_x_4367_, 3);
    if crate::leanh::lean_obj_tag(v_l_4371_) == 0 {
        let mut v_size_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_l_4371_);
        crate::leanh::lean_dec(v_h__1_4369_);
        v_size_4372_ = crate::leanh::lean_ctor_get(v_x_4367_, 0);
        crate::leanh::lean_inc(v_size_4372_);
        v_k_4373_ = crate::leanh::lean_ctor_get(v_x_4367_, 1);
        crate::leanh::lean_inc(v_k_4373_);
        v_v_4374_ = crate::leanh::lean_ctor_get(v_x_4367_, 2);
        crate::leanh::lean_inc(v_v_4374_);
        v_r_4375_ = crate::leanh::lean_ctor_get(v_x_4367_, 4);
        crate::leanh::lean_inc(v_r_4375_);
        crate::leanh::lean_dec(v_x_4367_);
        v_size_4376_ = crate::leanh::lean_ctor_get(v_l_4371_, 0);
        crate::leanh::lean_inc(v_size_4376_);
        v_k_4377_ = crate::leanh::lean_ctor_get(v_l_4371_, 1);
        crate::leanh::lean_inc(v_k_4377_);
        v_v_4378_ = crate::leanh::lean_ctor_get(v_l_4371_, 2);
        crate::leanh::lean_inc(v_v_4378_);
        v_l_4379_ = crate::leanh::lean_ctor_get(v_l_4371_, 3);
        crate::leanh::lean_inc(v_l_4379_);
        v_r_4380_ = crate::leanh::lean_ctor_get(v_l_4371_, 4);
        crate::leanh::lean_inc(v_r_4380_);
        crate::leanh::lean_dec_ref_known(v_l_4371_, 5);
        v___x_4381_ = crate::leanh::lean_apply_10(
            v_h__2_4370_,
            v_size_4372_,
            v_k_4373_,
            v_v_4374_,
            v_size_4376_,
            v_k_4377_,
            v_v_4378_,
            v_l_4379_,
            v_r_4380_,
            v_r_4375_,
            crate::leanh::lean_box(0),
        );
        return v___x_4381_;
    } else {
        let mut v_size_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4370_);
        v_size_4382_ = crate::leanh::lean_ctor_get(v_x_4367_, 0);
        crate::leanh::lean_inc(v_size_4382_);
        v_k_4383_ = crate::leanh::lean_ctor_get(v_x_4367_, 1);
        crate::leanh::lean_inc(v_k_4383_);
        v_v_4384_ = crate::leanh::lean_ctor_get(v_x_4367_, 2);
        crate::leanh::lean_inc(v_v_4384_);
        v_r_4385_ = crate::leanh::lean_ctor_get(v_x_4367_, 4);
        crate::leanh::lean_inc(v_r_4385_);
        crate::leanh::lean_dec(v_x_4367_);
        v___x_4386_ = crate::leanh::lean_apply_5(
            v_h__1_4369_,
            v_size_4382_,
            v_k_4383_,
            v_v_4384_,
            v_r_4385_,
            crate::leanh::lean_box(0),
        );
        return v___x_4386_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(
    mut v_x_4387_: *mut crate::leanh::LeanObject,
    mut v_h__1_4388_: *mut crate::leanh::LeanObject,
    mut v_h__2_4389_: *mut crate::leanh::LeanObject,
    mut v_h__3_4390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4387_) == 0 {
        let mut v_r_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4388_);
        v_r_4391_ = crate::leanh::lean_ctor_get(v_x_4387_, 4);
        if crate::leanh::lean_obj_tag(v_r_4391_) == 0 {
            let mut v_size_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4391_);
            crate::leanh::lean_dec(v_h__2_4389_);
            v_size_4392_ = crate::leanh::lean_ctor_get(v_x_4387_, 0);
            crate::leanh::lean_inc(v_size_4392_);
            v_k_4393_ = crate::leanh::lean_ctor_get(v_x_4387_, 1);
            crate::leanh::lean_inc(v_k_4393_);
            v_v_4394_ = crate::leanh::lean_ctor_get(v_x_4387_, 2);
            crate::leanh::lean_inc(v_v_4394_);
            v_l_4395_ = crate::leanh::lean_ctor_get(v_x_4387_, 3);
            crate::leanh::lean_inc(v_l_4395_);
            crate::leanh::lean_dec_ref_known(v_x_4387_, 5);
            v_size_4396_ = crate::leanh::lean_ctor_get(v_r_4391_, 0);
            crate::leanh::lean_inc(v_size_4396_);
            v_k_4397_ = crate::leanh::lean_ctor_get(v_r_4391_, 1);
            crate::leanh::lean_inc(v_k_4397_);
            v_v_4398_ = crate::leanh::lean_ctor_get(v_r_4391_, 2);
            crate::leanh::lean_inc(v_v_4398_);
            v_l_4399_ = crate::leanh::lean_ctor_get(v_r_4391_, 3);
            crate::leanh::lean_inc(v_l_4399_);
            v_r_4400_ = crate::leanh::lean_ctor_get(v_r_4391_, 4);
            crate::leanh::lean_inc(v_r_4400_);
            crate::leanh::lean_dec_ref_known(v_r_4391_, 5);
            v___x_4401_ = crate::leanh::lean_apply_9(
                v_h__3_4390_,
                v_size_4392_,
                v_k_4393_,
                v_v_4394_,
                v_l_4395_,
                v_size_4396_,
                v_k_4397_,
                v_v_4398_,
                v_l_4399_,
                v_r_4400_,
            );
            return v___x_4401_;
        } else {
            let mut v_size_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4390_);
            v_size_4402_ = crate::leanh::lean_ctor_get(v_x_4387_, 0);
            crate::leanh::lean_inc(v_size_4402_);
            v_k_4403_ = crate::leanh::lean_ctor_get(v_x_4387_, 1);
            crate::leanh::lean_inc(v_k_4403_);
            v_v_4404_ = crate::leanh::lean_ctor_get(v_x_4387_, 2);
            crate::leanh::lean_inc(v_v_4404_);
            v_l_4405_ = crate::leanh::lean_ctor_get(v_x_4387_, 3);
            crate::leanh::lean_inc(v_l_4405_);
            crate::leanh::lean_dec_ref_known(v_x_4387_, 5);
            v___x_4406_ = crate::leanh::lean_apply_4(
                v_h__2_4389_,
                v_size_4402_,
                v_k_4403_,
                v_v_4404_,
                v_l_4405_,
            );
            return v___x_4406_;
        }
    } else {
        let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4390_);
        crate::leanh::lean_dec(v_h__2_4389_);
        v___x_4407_ = crate::leanh::lean_box(0);
        v___x_4408_ = crate::leanh::lean_apply_1(v_h__1_4388_, v___x_4407_);
        return v___x_4408_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4409_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4410_: *mut crate::leanh::LeanObject,
    mut v_motive_4411_: *mut crate::leanh::LeanObject,
    mut v_x_4412_: *mut crate::leanh::LeanObject,
    mut v_h__1_4413_: *mut crate::leanh::LeanObject,
    mut v_h__2_4414_: *mut crate::leanh::LeanObject,
    mut v_h__3_4415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4412_) == 0 {
        let mut v_r_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4413_);
        v_r_4416_ = crate::leanh::lean_ctor_get(v_x_4412_, 4);
        if crate::leanh::lean_obj_tag(v_r_4416_) == 0 {
            let mut v_size_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4416_);
            crate::leanh::lean_dec(v_h__2_4414_);
            v_size_4417_ = crate::leanh::lean_ctor_get(v_x_4412_, 0);
            crate::leanh::lean_inc(v_size_4417_);
            v_k_4418_ = crate::leanh::lean_ctor_get(v_x_4412_, 1);
            crate::leanh::lean_inc(v_k_4418_);
            v_v_4419_ = crate::leanh::lean_ctor_get(v_x_4412_, 2);
            crate::leanh::lean_inc(v_v_4419_);
            v_l_4420_ = crate::leanh::lean_ctor_get(v_x_4412_, 3);
            crate::leanh::lean_inc(v_l_4420_);
            crate::leanh::lean_dec_ref_known(v_x_4412_, 5);
            v_size_4421_ = crate::leanh::lean_ctor_get(v_r_4416_, 0);
            crate::leanh::lean_inc(v_size_4421_);
            v_k_4422_ = crate::leanh::lean_ctor_get(v_r_4416_, 1);
            crate::leanh::lean_inc(v_k_4422_);
            v_v_4423_ = crate::leanh::lean_ctor_get(v_r_4416_, 2);
            crate::leanh::lean_inc(v_v_4423_);
            v_l_4424_ = crate::leanh::lean_ctor_get(v_r_4416_, 3);
            crate::leanh::lean_inc(v_l_4424_);
            v_r_4425_ = crate::leanh::lean_ctor_get(v_r_4416_, 4);
            crate::leanh::lean_inc(v_r_4425_);
            crate::leanh::lean_dec_ref_known(v_r_4416_, 5);
            v___x_4426_ = crate::leanh::lean_apply_9(
                v_h__3_4415_,
                v_size_4417_,
                v_k_4418_,
                v_v_4419_,
                v_l_4420_,
                v_size_4421_,
                v_k_4422_,
                v_v_4423_,
                v_l_4424_,
                v_r_4425_,
            );
            return v___x_4426_;
        } else {
            let mut v_size_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4415_);
            v_size_4427_ = crate::leanh::lean_ctor_get(v_x_4412_, 0);
            crate::leanh::lean_inc(v_size_4427_);
            v_k_4428_ = crate::leanh::lean_ctor_get(v_x_4412_, 1);
            crate::leanh::lean_inc(v_k_4428_);
            v_v_4429_ = crate::leanh::lean_ctor_get(v_x_4412_, 2);
            crate::leanh::lean_inc(v_v_4429_);
            v_l_4430_ = crate::leanh::lean_ctor_get(v_x_4412_, 3);
            crate::leanh::lean_inc(v_l_4430_);
            crate::leanh::lean_dec_ref_known(v_x_4412_, 5);
            v___x_4431_ = crate::leanh::lean_apply_4(
                v_h__2_4414_,
                v_size_4427_,
                v_k_4428_,
                v_v_4429_,
                v_l_4430_,
            );
            return v___x_4431_;
        }
    } else {
        let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4415_);
        crate::leanh::lean_dec(v_h__2_4414_);
        v___x_4432_ = crate::leanh::lean_box(0);
        v___x_4433_ = crate::leanh::lean_apply_1(v_h__1_4413_, v___x_4432_);
        return v___x_4433_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(
    mut v_x_4434_: *mut crate::leanh::LeanObject,
    mut v_x_4435_: *mut crate::leanh::LeanObject,
    mut v_h__1_4436_: *mut crate::leanh::LeanObject,
    mut v_h__2_4437_: *mut crate::leanh::LeanObject,
    mut v_h__3_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4434_) == 0 {
        let mut v_r_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4436_);
        v_r_4439_ = crate::leanh::lean_ctor_get(v_x_4434_, 4);
        if crate::leanh::lean_obj_tag(v_r_4439_) == 0 {
            let mut v_size_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4439_);
            crate::leanh::lean_dec(v_h__2_4437_);
            v_size_4440_ = crate::leanh::lean_ctor_get(v_x_4434_, 0);
            crate::leanh::lean_inc(v_size_4440_);
            v_k_4441_ = crate::leanh::lean_ctor_get(v_x_4434_, 1);
            crate::leanh::lean_inc(v_k_4441_);
            v_v_4442_ = crate::leanh::lean_ctor_get(v_x_4434_, 2);
            crate::leanh::lean_inc(v_v_4442_);
            v_l_4443_ = crate::leanh::lean_ctor_get(v_x_4434_, 3);
            crate::leanh::lean_inc(v_l_4443_);
            crate::leanh::lean_dec_ref_known(v_x_4434_, 5);
            v_size_4444_ = crate::leanh::lean_ctor_get(v_r_4439_, 0);
            crate::leanh::lean_inc(v_size_4444_);
            v_k_4445_ = crate::leanh::lean_ctor_get(v_r_4439_, 1);
            crate::leanh::lean_inc(v_k_4445_);
            v_v_4446_ = crate::leanh::lean_ctor_get(v_r_4439_, 2);
            crate::leanh::lean_inc(v_v_4446_);
            v_l_4447_ = crate::leanh::lean_ctor_get(v_r_4439_, 3);
            crate::leanh::lean_inc(v_l_4447_);
            v_r_4448_ = crate::leanh::lean_ctor_get(v_r_4439_, 4);
            crate::leanh::lean_inc(v_r_4448_);
            crate::leanh::lean_dec_ref_known(v_r_4439_, 5);
            v___x_4449_ = crate::leanh::lean_apply_10(
                v_h__3_4438_,
                v_size_4440_,
                v_k_4441_,
                v_v_4442_,
                v_l_4443_,
                v_size_4444_,
                v_k_4445_,
                v_v_4446_,
                v_l_4447_,
                v_r_4448_,
                v_x_4435_,
            );
            return v___x_4449_;
        } else {
            let mut v_size_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4438_);
            v_size_4450_ = crate::leanh::lean_ctor_get(v_x_4434_, 0);
            crate::leanh::lean_inc(v_size_4450_);
            v_k_4451_ = crate::leanh::lean_ctor_get(v_x_4434_, 1);
            crate::leanh::lean_inc(v_k_4451_);
            v_v_4452_ = crate::leanh::lean_ctor_get(v_x_4434_, 2);
            crate::leanh::lean_inc(v_v_4452_);
            v_l_4453_ = crate::leanh::lean_ctor_get(v_x_4434_, 3);
            crate::leanh::lean_inc(v_l_4453_);
            crate::leanh::lean_dec_ref_known(v_x_4434_, 5);
            v___x_4454_ = crate::leanh::lean_apply_5(
                v_h__2_4437_,
                v_size_4450_,
                v_k_4451_,
                v_v_4452_,
                v_l_4453_,
                v_x_4435_,
            );
            return v___x_4454_;
        }
    } else {
        let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4438_);
        crate::leanh::lean_dec(v_h__2_4437_);
        v___x_4455_ = crate::leanh::lean_apply_1(v_h__1_4436_, v_x_4435_);
        return v___x_4455_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(
    mut v_00_u03b1_4456_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4457_: *mut crate::leanh::LeanObject,
    mut v_motive_4458_: *mut crate::leanh::LeanObject,
    mut v_x_4459_: *mut crate::leanh::LeanObject,
    mut v_x_4460_: *mut crate::leanh::LeanObject,
    mut v_h__1_4461_: *mut crate::leanh::LeanObject,
    mut v_h__2_4462_: *mut crate::leanh::LeanObject,
    mut v_h__3_4463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4459_) == 0 {
        let mut v_r_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4461_);
        v_r_4464_ = crate::leanh::lean_ctor_get(v_x_4459_, 4);
        if crate::leanh::lean_obj_tag(v_r_4464_) == 0 {
            let mut v_size_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4464_);
            crate::leanh::lean_dec(v_h__2_4462_);
            v_size_4465_ = crate::leanh::lean_ctor_get(v_x_4459_, 0);
            crate::leanh::lean_inc(v_size_4465_);
            v_k_4466_ = crate::leanh::lean_ctor_get(v_x_4459_, 1);
            crate::leanh::lean_inc(v_k_4466_);
            v_v_4467_ = crate::leanh::lean_ctor_get(v_x_4459_, 2);
            crate::leanh::lean_inc(v_v_4467_);
            v_l_4468_ = crate::leanh::lean_ctor_get(v_x_4459_, 3);
            crate::leanh::lean_inc(v_l_4468_);
            crate::leanh::lean_dec_ref_known(v_x_4459_, 5);
            v_size_4469_ = crate::leanh::lean_ctor_get(v_r_4464_, 0);
            crate::leanh::lean_inc(v_size_4469_);
            v_k_4470_ = crate::leanh::lean_ctor_get(v_r_4464_, 1);
            crate::leanh::lean_inc(v_k_4470_);
            v_v_4471_ = crate::leanh::lean_ctor_get(v_r_4464_, 2);
            crate::leanh::lean_inc(v_v_4471_);
            v_l_4472_ = crate::leanh::lean_ctor_get(v_r_4464_, 3);
            crate::leanh::lean_inc(v_l_4472_);
            v_r_4473_ = crate::leanh::lean_ctor_get(v_r_4464_, 4);
            crate::leanh::lean_inc(v_r_4473_);
            crate::leanh::lean_dec_ref_known(v_r_4464_, 5);
            v___x_4474_ = crate::leanh::lean_apply_10(
                v_h__3_4463_,
                v_size_4465_,
                v_k_4466_,
                v_v_4467_,
                v_l_4468_,
                v_size_4469_,
                v_k_4470_,
                v_v_4471_,
                v_l_4472_,
                v_r_4473_,
                v_x_4460_,
            );
            return v___x_4474_;
        } else {
            let mut v_size_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4463_);
            v_size_4475_ = crate::leanh::lean_ctor_get(v_x_4459_, 0);
            crate::leanh::lean_inc(v_size_4475_);
            v_k_4476_ = crate::leanh::lean_ctor_get(v_x_4459_, 1);
            crate::leanh::lean_inc(v_k_4476_);
            v_v_4477_ = crate::leanh::lean_ctor_get(v_x_4459_, 2);
            crate::leanh::lean_inc(v_v_4477_);
            v_l_4478_ = crate::leanh::lean_ctor_get(v_x_4459_, 3);
            crate::leanh::lean_inc(v_l_4478_);
            crate::leanh::lean_dec_ref_known(v_x_4459_, 5);
            v___x_4479_ = crate::leanh::lean_apply_5(
                v_h__2_4462_,
                v_size_4475_,
                v_k_4476_,
                v_v_4477_,
                v_l_4478_,
                v_x_4460_,
            );
            return v___x_4479_;
        }
    } else {
        let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4463_);
        crate::leanh::lean_dec(v_h__2_4462_);
        v___x_4480_ = crate::leanh::lean_apply_1(v_h__1_4461_, v_x_4460_);
        return v___x_4480_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(
    mut v_x_4481_: *mut crate::leanh::LeanObject,
    mut v_h__1_4482_: *mut crate::leanh::LeanObject,
    mut v_h__2_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_4484_ = crate::leanh::lean_ctor_get(v_x_4481_, 4);
    if crate::leanh::lean_obj_tag(v_r_4484_) == 0 {
        let mut v_size_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_r_4484_);
        crate::leanh::lean_dec(v_h__1_4482_);
        v_size_4485_ = crate::leanh::lean_ctor_get(v_x_4481_, 0);
        crate::leanh::lean_inc(v_size_4485_);
        v_k_4486_ = crate::leanh::lean_ctor_get(v_x_4481_, 1);
        crate::leanh::lean_inc(v_k_4486_);
        v_v_4487_ = crate::leanh::lean_ctor_get(v_x_4481_, 2);
        crate::leanh::lean_inc(v_v_4487_);
        v_l_4488_ = crate::leanh::lean_ctor_get(v_x_4481_, 3);
        crate::leanh::lean_inc(v_l_4488_);
        crate::leanh::lean_dec(v_x_4481_);
        v_size_4489_ = crate::leanh::lean_ctor_get(v_r_4484_, 0);
        crate::leanh::lean_inc(v_size_4489_);
        v_k_4490_ = crate::leanh::lean_ctor_get(v_r_4484_, 1);
        crate::leanh::lean_inc(v_k_4490_);
        v_v_4491_ = crate::leanh::lean_ctor_get(v_r_4484_, 2);
        crate::leanh::lean_inc(v_v_4491_);
        v_l_4492_ = crate::leanh::lean_ctor_get(v_r_4484_, 3);
        crate::leanh::lean_inc(v_l_4492_);
        v_r_4493_ = crate::leanh::lean_ctor_get(v_r_4484_, 4);
        crate::leanh::lean_inc(v_r_4493_);
        crate::leanh::lean_dec_ref_known(v_r_4484_, 5);
        v___x_4494_ = crate::leanh::lean_apply_10(
            v_h__2_4483_,
            v_size_4485_,
            v_k_4486_,
            v_v_4487_,
            v_l_4488_,
            v_size_4489_,
            v_k_4490_,
            v_v_4491_,
            v_l_4492_,
            v_r_4493_,
            crate::leanh::lean_box(0),
        );
        return v___x_4494_;
    } else {
        let mut v_size_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4483_);
        v_size_4495_ = crate::leanh::lean_ctor_get(v_x_4481_, 0);
        crate::leanh::lean_inc(v_size_4495_);
        v_k_4496_ = crate::leanh::lean_ctor_get(v_x_4481_, 1);
        crate::leanh::lean_inc(v_k_4496_);
        v_v_4497_ = crate::leanh::lean_ctor_get(v_x_4481_, 2);
        crate::leanh::lean_inc(v_v_4497_);
        v_l_4498_ = crate::leanh::lean_ctor_get(v_x_4481_, 3);
        crate::leanh::lean_inc(v_l_4498_);
        crate::leanh::lean_dec(v_x_4481_);
        v___x_4499_ = crate::leanh::lean_apply_5(
            v_h__1_4482_,
            v_size_4495_,
            v_k_4496_,
            v_v_4497_,
            v_l_4498_,
            crate::leanh::lean_box(0),
        );
        return v___x_4499_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(
    mut v_00_u03b1_4500_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4501_: *mut crate::leanh::LeanObject,
    mut v_motive_4502_: *mut crate::leanh::LeanObject,
    mut v_x_4503_: *mut crate::leanh::LeanObject,
    mut v_x_4504_: *mut crate::leanh::LeanObject,
    mut v_h__1_4505_: *mut crate::leanh::LeanObject,
    mut v_h__2_4506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_4507_ = crate::leanh::lean_ctor_get(v_x_4503_, 4);
    if crate::leanh::lean_obj_tag(v_r_4507_) == 0 {
        let mut v_size_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_r_4507_);
        crate::leanh::lean_dec(v_h__1_4505_);
        v_size_4508_ = crate::leanh::lean_ctor_get(v_x_4503_, 0);
        crate::leanh::lean_inc(v_size_4508_);
        v_k_4509_ = crate::leanh::lean_ctor_get(v_x_4503_, 1);
        crate::leanh::lean_inc(v_k_4509_);
        v_v_4510_ = crate::leanh::lean_ctor_get(v_x_4503_, 2);
        crate::leanh::lean_inc(v_v_4510_);
        v_l_4511_ = crate::leanh::lean_ctor_get(v_x_4503_, 3);
        crate::leanh::lean_inc(v_l_4511_);
        crate::leanh::lean_dec(v_x_4503_);
        v_size_4512_ = crate::leanh::lean_ctor_get(v_r_4507_, 0);
        crate::leanh::lean_inc(v_size_4512_);
        v_k_4513_ = crate::leanh::lean_ctor_get(v_r_4507_, 1);
        crate::leanh::lean_inc(v_k_4513_);
        v_v_4514_ = crate::leanh::lean_ctor_get(v_r_4507_, 2);
        crate::leanh::lean_inc(v_v_4514_);
        v_l_4515_ = crate::leanh::lean_ctor_get(v_r_4507_, 3);
        crate::leanh::lean_inc(v_l_4515_);
        v_r_4516_ = crate::leanh::lean_ctor_get(v_r_4507_, 4);
        crate::leanh::lean_inc(v_r_4516_);
        crate::leanh::lean_dec_ref_known(v_r_4507_, 5);
        v___x_4517_ = crate::leanh::lean_apply_10(
            v_h__2_4506_,
            v_size_4508_,
            v_k_4509_,
            v_v_4510_,
            v_l_4511_,
            v_size_4512_,
            v_k_4513_,
            v_v_4514_,
            v_l_4515_,
            v_r_4516_,
            crate::leanh::lean_box(0),
        );
        return v___x_4517_;
    } else {
        let mut v_size_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4506_);
        v_size_4518_ = crate::leanh::lean_ctor_get(v_x_4503_, 0);
        crate::leanh::lean_inc(v_size_4518_);
        v_k_4519_ = crate::leanh::lean_ctor_get(v_x_4503_, 1);
        crate::leanh::lean_inc(v_k_4519_);
        v_v_4520_ = crate::leanh::lean_ctor_get(v_x_4503_, 2);
        crate::leanh::lean_inc(v_v_4520_);
        v_l_4521_ = crate::leanh::lean_ctor_get(v_x_4503_, 3);
        crate::leanh::lean_inc(v_l_4521_);
        crate::leanh::lean_dec(v_x_4503_);
        v___x_4522_ = crate::leanh::lean_apply_5(
            v_h__1_4505_,
            v_size_4518_,
            v_k_4519_,
            v_v_4520_,
            v_l_4521_,
            crate::leanh::lean_box(0),
        );
        return v___x_4522_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(
    mut v_x_4523_: *mut crate::leanh::LeanObject,
    mut v_x_4524_: *mut crate::leanh::LeanObject,
    mut v_h__1_4525_: *mut crate::leanh::LeanObject,
    mut v_h__2_4526_: *mut crate::leanh::LeanObject,
    mut v_h__3_4527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4523_) == 0 {
        let mut v_l_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4525_);
        v_l_4528_ = crate::leanh::lean_ctor_get(v_x_4523_, 3);
        if crate::leanh::lean_obj_tag(v_l_4528_) == 0 {
            let mut v_size_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4528_);
            crate::leanh::lean_dec(v_h__2_4526_);
            v_size_4529_ = crate::leanh::lean_ctor_get(v_x_4523_, 0);
            crate::leanh::lean_inc(v_size_4529_);
            v_k_4530_ = crate::leanh::lean_ctor_get(v_x_4523_, 1);
            crate::leanh::lean_inc(v_k_4530_);
            v_v_4531_ = crate::leanh::lean_ctor_get(v_x_4523_, 2);
            crate::leanh::lean_inc(v_v_4531_);
            v_r_4532_ = crate::leanh::lean_ctor_get(v_x_4523_, 4);
            crate::leanh::lean_inc(v_r_4532_);
            crate::leanh::lean_dec_ref_known(v_x_4523_, 5);
            v_size_4533_ = crate::leanh::lean_ctor_get(v_l_4528_, 0);
            crate::leanh::lean_inc(v_size_4533_);
            v_k_4534_ = crate::leanh::lean_ctor_get(v_l_4528_, 1);
            crate::leanh::lean_inc(v_k_4534_);
            v_v_4535_ = crate::leanh::lean_ctor_get(v_l_4528_, 2);
            crate::leanh::lean_inc(v_v_4535_);
            v_l_4536_ = crate::leanh::lean_ctor_get(v_l_4528_, 3);
            crate::leanh::lean_inc(v_l_4536_);
            v_r_4537_ = crate::leanh::lean_ctor_get(v_l_4528_, 4);
            crate::leanh::lean_inc(v_r_4537_);
            crate::leanh::lean_dec_ref_known(v_l_4528_, 5);
            v___x_4538_ = crate::leanh::lean_apply_10(
                v_h__3_4527_,
                v_size_4529_,
                v_k_4530_,
                v_v_4531_,
                v_size_4533_,
                v_k_4534_,
                v_v_4535_,
                v_l_4536_,
                v_r_4537_,
                v_r_4532_,
                v_x_4524_,
            );
            return v___x_4538_;
        } else {
            let mut v_size_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4527_);
            v_size_4539_ = crate::leanh::lean_ctor_get(v_x_4523_, 0);
            crate::leanh::lean_inc(v_size_4539_);
            v_k_4540_ = crate::leanh::lean_ctor_get(v_x_4523_, 1);
            crate::leanh::lean_inc(v_k_4540_);
            v_v_4541_ = crate::leanh::lean_ctor_get(v_x_4523_, 2);
            crate::leanh::lean_inc(v_v_4541_);
            v_r_4542_ = crate::leanh::lean_ctor_get(v_x_4523_, 4);
            crate::leanh::lean_inc(v_r_4542_);
            crate::leanh::lean_dec_ref_known(v_x_4523_, 5);
            v___x_4543_ = crate::leanh::lean_apply_5(
                v_h__2_4526_,
                v_size_4539_,
                v_k_4540_,
                v_v_4541_,
                v_r_4542_,
                v_x_4524_,
            );
            return v___x_4543_;
        }
    } else {
        let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4527_);
        crate::leanh::lean_dec(v_h__2_4526_);
        v___x_4544_ = crate::leanh::lean_apply_1(v_h__1_4525_, v_x_4524_);
        return v___x_4544_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(
    mut v_00_u03b1_4545_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4546_: *mut crate::leanh::LeanObject,
    mut v_motive_4547_: *mut crate::leanh::LeanObject,
    mut v_x_4548_: *mut crate::leanh::LeanObject,
    mut v_x_4549_: *mut crate::leanh::LeanObject,
    mut v_h__1_4550_: *mut crate::leanh::LeanObject,
    mut v_h__2_4551_: *mut crate::leanh::LeanObject,
    mut v_h__3_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4548_) == 0 {
        let mut v_l_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4550_);
        v_l_4553_ = crate::leanh::lean_ctor_get(v_x_4548_, 3);
        if crate::leanh::lean_obj_tag(v_l_4553_) == 0 {
            let mut v_size_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4553_);
            crate::leanh::lean_dec(v_h__2_4551_);
            v_size_4554_ = crate::leanh::lean_ctor_get(v_x_4548_, 0);
            crate::leanh::lean_inc(v_size_4554_);
            v_k_4555_ = crate::leanh::lean_ctor_get(v_x_4548_, 1);
            crate::leanh::lean_inc(v_k_4555_);
            v_v_4556_ = crate::leanh::lean_ctor_get(v_x_4548_, 2);
            crate::leanh::lean_inc(v_v_4556_);
            v_r_4557_ = crate::leanh::lean_ctor_get(v_x_4548_, 4);
            crate::leanh::lean_inc(v_r_4557_);
            crate::leanh::lean_dec_ref_known(v_x_4548_, 5);
            v_size_4558_ = crate::leanh::lean_ctor_get(v_l_4553_, 0);
            crate::leanh::lean_inc(v_size_4558_);
            v_k_4559_ = crate::leanh::lean_ctor_get(v_l_4553_, 1);
            crate::leanh::lean_inc(v_k_4559_);
            v_v_4560_ = crate::leanh::lean_ctor_get(v_l_4553_, 2);
            crate::leanh::lean_inc(v_v_4560_);
            v_l_4561_ = crate::leanh::lean_ctor_get(v_l_4553_, 3);
            crate::leanh::lean_inc(v_l_4561_);
            v_r_4562_ = crate::leanh::lean_ctor_get(v_l_4553_, 4);
            crate::leanh::lean_inc(v_r_4562_);
            crate::leanh::lean_dec_ref_known(v_l_4553_, 5);
            v___x_4563_ = crate::leanh::lean_apply_10(
                v_h__3_4552_,
                v_size_4554_,
                v_k_4555_,
                v_v_4556_,
                v_size_4558_,
                v_k_4559_,
                v_v_4560_,
                v_l_4561_,
                v_r_4562_,
                v_r_4557_,
                v_x_4549_,
            );
            return v___x_4563_;
        } else {
            let mut v_size_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4552_);
            v_size_4564_ = crate::leanh::lean_ctor_get(v_x_4548_, 0);
            crate::leanh::lean_inc(v_size_4564_);
            v_k_4565_ = crate::leanh::lean_ctor_get(v_x_4548_, 1);
            crate::leanh::lean_inc(v_k_4565_);
            v_v_4566_ = crate::leanh::lean_ctor_get(v_x_4548_, 2);
            crate::leanh::lean_inc(v_v_4566_);
            v_r_4567_ = crate::leanh::lean_ctor_get(v_x_4548_, 4);
            crate::leanh::lean_inc(v_r_4567_);
            crate::leanh::lean_dec_ref_known(v_x_4548_, 5);
            v___x_4568_ = crate::leanh::lean_apply_5(
                v_h__2_4551_,
                v_size_4564_,
                v_k_4565_,
                v_v_4566_,
                v_r_4567_,
                v_x_4549_,
            );
            return v___x_4568_;
        }
    } else {
        let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4552_);
        crate::leanh::lean_dec(v_h__2_4551_);
        v___x_4569_ = crate::leanh::lean_apply_1(v_h__1_4550_, v_x_4549_);
        return v___x_4569_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(
    mut v_x_4570_: *mut crate::leanh::LeanObject,
    mut v_x_4571_: *mut crate::leanh::LeanObject,
    mut v_h__1_4572_: *mut crate::leanh::LeanObject,
    mut v_h__2_4573_: *mut crate::leanh::LeanObject,
    mut v_h__3_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4570_) == 0 {
        let mut v_r_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4572_);
        v_r_4575_ = crate::leanh::lean_ctor_get(v_x_4570_, 4);
        if crate::leanh::lean_obj_tag(v_r_4575_) == 0 {
            let mut v_size_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4575_);
            crate::leanh::lean_dec(v_h__2_4573_);
            v_size_4576_ = crate::leanh::lean_ctor_get(v_x_4570_, 0);
            crate::leanh::lean_inc(v_size_4576_);
            v_k_4577_ = crate::leanh::lean_ctor_get(v_x_4570_, 1);
            crate::leanh::lean_inc(v_k_4577_);
            v_v_4578_ = crate::leanh::lean_ctor_get(v_x_4570_, 2);
            crate::leanh::lean_inc(v_v_4578_);
            v_l_4579_ = crate::leanh::lean_ctor_get(v_x_4570_, 3);
            crate::leanh::lean_inc(v_l_4579_);
            crate::leanh::lean_dec_ref_known(v_x_4570_, 5);
            v_size_4580_ = crate::leanh::lean_ctor_get(v_r_4575_, 0);
            crate::leanh::lean_inc(v_size_4580_);
            v_k_4581_ = crate::leanh::lean_ctor_get(v_r_4575_, 1);
            crate::leanh::lean_inc(v_k_4581_);
            v_v_4582_ = crate::leanh::lean_ctor_get(v_r_4575_, 2);
            crate::leanh::lean_inc(v_v_4582_);
            v_l_4583_ = crate::leanh::lean_ctor_get(v_r_4575_, 3);
            crate::leanh::lean_inc(v_l_4583_);
            v_r_4584_ = crate::leanh::lean_ctor_get(v_r_4575_, 4);
            crate::leanh::lean_inc(v_r_4584_);
            crate::leanh::lean_dec_ref_known(v_r_4575_, 5);
            v___x_4585_ = crate::leanh::lean_apply_10(
                v_h__3_4574_,
                v_size_4576_,
                v_k_4577_,
                v_v_4578_,
                v_l_4579_,
                v_size_4580_,
                v_k_4581_,
                v_v_4582_,
                v_l_4583_,
                v_r_4584_,
                v_x_4571_,
            );
            return v___x_4585_;
        } else {
            let mut v_size_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4574_);
            v_size_4586_ = crate::leanh::lean_ctor_get(v_x_4570_, 0);
            crate::leanh::lean_inc(v_size_4586_);
            v_k_4587_ = crate::leanh::lean_ctor_get(v_x_4570_, 1);
            crate::leanh::lean_inc(v_k_4587_);
            v_v_4588_ = crate::leanh::lean_ctor_get(v_x_4570_, 2);
            crate::leanh::lean_inc(v_v_4588_);
            v_l_4589_ = crate::leanh::lean_ctor_get(v_x_4570_, 3);
            crate::leanh::lean_inc(v_l_4589_);
            crate::leanh::lean_dec_ref_known(v_x_4570_, 5);
            v___x_4590_ = crate::leanh::lean_apply_5(
                v_h__2_4573_,
                v_size_4586_,
                v_k_4587_,
                v_v_4588_,
                v_l_4589_,
                v_x_4571_,
            );
            return v___x_4590_;
        }
    } else {
        let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4574_);
        crate::leanh::lean_dec(v_h__2_4573_);
        v___x_4591_ = crate::leanh::lean_apply_1(v_h__1_4572_, v_x_4571_);
        return v___x_4591_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(
    mut v_00_u03b1_4592_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4593_: *mut crate::leanh::LeanObject,
    mut v_motive_4594_: *mut crate::leanh::LeanObject,
    mut v_x_4595_: *mut crate::leanh::LeanObject,
    mut v_x_4596_: *mut crate::leanh::LeanObject,
    mut v_h__1_4597_: *mut crate::leanh::LeanObject,
    mut v_h__2_4598_: *mut crate::leanh::LeanObject,
    mut v_h__3_4599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4595_) == 0 {
        let mut v_r_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4597_);
        v_r_4600_ = crate::leanh::lean_ctor_get(v_x_4595_, 4);
        if crate::leanh::lean_obj_tag(v_r_4600_) == 0 {
            let mut v_size_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4600_);
            crate::leanh::lean_dec(v_h__2_4598_);
            v_size_4601_ = crate::leanh::lean_ctor_get(v_x_4595_, 0);
            crate::leanh::lean_inc(v_size_4601_);
            v_k_4602_ = crate::leanh::lean_ctor_get(v_x_4595_, 1);
            crate::leanh::lean_inc(v_k_4602_);
            v_v_4603_ = crate::leanh::lean_ctor_get(v_x_4595_, 2);
            crate::leanh::lean_inc(v_v_4603_);
            v_l_4604_ = crate::leanh::lean_ctor_get(v_x_4595_, 3);
            crate::leanh::lean_inc(v_l_4604_);
            crate::leanh::lean_dec_ref_known(v_x_4595_, 5);
            v_size_4605_ = crate::leanh::lean_ctor_get(v_r_4600_, 0);
            crate::leanh::lean_inc(v_size_4605_);
            v_k_4606_ = crate::leanh::lean_ctor_get(v_r_4600_, 1);
            crate::leanh::lean_inc(v_k_4606_);
            v_v_4607_ = crate::leanh::lean_ctor_get(v_r_4600_, 2);
            crate::leanh::lean_inc(v_v_4607_);
            v_l_4608_ = crate::leanh::lean_ctor_get(v_r_4600_, 3);
            crate::leanh::lean_inc(v_l_4608_);
            v_r_4609_ = crate::leanh::lean_ctor_get(v_r_4600_, 4);
            crate::leanh::lean_inc(v_r_4609_);
            crate::leanh::lean_dec_ref_known(v_r_4600_, 5);
            v___x_4610_ = crate::leanh::lean_apply_10(
                v_h__3_4599_,
                v_size_4601_,
                v_k_4602_,
                v_v_4603_,
                v_l_4604_,
                v_size_4605_,
                v_k_4606_,
                v_v_4607_,
                v_l_4608_,
                v_r_4609_,
                v_x_4596_,
            );
            return v___x_4610_;
        } else {
            let mut v_size_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4599_);
            v_size_4611_ = crate::leanh::lean_ctor_get(v_x_4595_, 0);
            crate::leanh::lean_inc(v_size_4611_);
            v_k_4612_ = crate::leanh::lean_ctor_get(v_x_4595_, 1);
            crate::leanh::lean_inc(v_k_4612_);
            v_v_4613_ = crate::leanh::lean_ctor_get(v_x_4595_, 2);
            crate::leanh::lean_inc(v_v_4613_);
            v_l_4614_ = crate::leanh::lean_ctor_get(v_x_4595_, 3);
            crate::leanh::lean_inc(v_l_4614_);
            crate::leanh::lean_dec_ref_known(v_x_4595_, 5);
            v___x_4615_ = crate::leanh::lean_apply_5(
                v_h__2_4598_,
                v_size_4611_,
                v_k_4612_,
                v_v_4613_,
                v_l_4614_,
                v_x_4596_,
            );
            return v___x_4615_;
        }
    } else {
        let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4599_);
        crate::leanh::lean_dec(v_h__2_4598_);
        v___x_4616_ = crate::leanh::lean_apply_1(v_h__1_4597_, v_x_4596_);
        return v___x_4616_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(
    mut v_x_4617_: *mut crate::leanh::LeanObject,
    mut v_h__1_4618_: *mut crate::leanh::LeanObject,
    mut v_h__2_4619_: *mut crate::leanh::LeanObject,
    mut v_h__3_4620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4617_) == 0 {
        let mut v_l_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4618_);
        v_l_4621_ = crate::leanh::lean_ctor_get(v_x_4617_, 3);
        if crate::leanh::lean_obj_tag(v_l_4621_) == 0 {
            let mut v_size_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4621_);
            crate::leanh::lean_dec(v_h__2_4619_);
            v_size_4622_ = crate::leanh::lean_ctor_get(v_x_4617_, 0);
            crate::leanh::lean_inc(v_size_4622_);
            v_k_4623_ = crate::leanh::lean_ctor_get(v_x_4617_, 1);
            crate::leanh::lean_inc(v_k_4623_);
            v_v_4624_ = crate::leanh::lean_ctor_get(v_x_4617_, 2);
            crate::leanh::lean_inc(v_v_4624_);
            v_r_4625_ = crate::leanh::lean_ctor_get(v_x_4617_, 4);
            crate::leanh::lean_inc(v_r_4625_);
            crate::leanh::lean_dec_ref_known(v_x_4617_, 5);
            v_size_4626_ = crate::leanh::lean_ctor_get(v_l_4621_, 0);
            crate::leanh::lean_inc(v_size_4626_);
            v_k_4627_ = crate::leanh::lean_ctor_get(v_l_4621_, 1);
            crate::leanh::lean_inc(v_k_4627_);
            v_v_4628_ = crate::leanh::lean_ctor_get(v_l_4621_, 2);
            crate::leanh::lean_inc(v_v_4628_);
            v_l_4629_ = crate::leanh::lean_ctor_get(v_l_4621_, 3);
            crate::leanh::lean_inc(v_l_4629_);
            v_r_4630_ = crate::leanh::lean_ctor_get(v_l_4621_, 4);
            crate::leanh::lean_inc(v_r_4630_);
            crate::leanh::lean_dec_ref_known(v_l_4621_, 5);
            v___x_4631_ = crate::leanh::lean_apply_9(
                v_h__3_4620_,
                v_size_4622_,
                v_k_4623_,
                v_v_4624_,
                v_size_4626_,
                v_k_4627_,
                v_v_4628_,
                v_l_4629_,
                v_r_4630_,
                v_r_4625_,
            );
            return v___x_4631_;
        } else {
            let mut v_size_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4620_);
            v_size_4632_ = crate::leanh::lean_ctor_get(v_x_4617_, 0);
            crate::leanh::lean_inc(v_size_4632_);
            v_k_4633_ = crate::leanh::lean_ctor_get(v_x_4617_, 1);
            crate::leanh::lean_inc(v_k_4633_);
            v_v_4634_ = crate::leanh::lean_ctor_get(v_x_4617_, 2);
            crate::leanh::lean_inc(v_v_4634_);
            v_r_4635_ = crate::leanh::lean_ctor_get(v_x_4617_, 4);
            crate::leanh::lean_inc(v_r_4635_);
            crate::leanh::lean_dec_ref_known(v_x_4617_, 5);
            v___x_4636_ = crate::leanh::lean_apply_4(
                v_h__2_4619_,
                v_size_4632_,
                v_k_4633_,
                v_v_4634_,
                v_r_4635_,
            );
            return v___x_4636_;
        }
    } else {
        let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4620_);
        crate::leanh::lean_dec(v_h__2_4619_);
        v___x_4637_ = crate::leanh::lean_box(0);
        v___x_4638_ = crate::leanh::lean_apply_1(v_h__1_4618_, v___x_4637_);
        return v___x_4638_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4639_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4640_: *mut crate::leanh::LeanObject,
    mut v_motive_4641_: *mut crate::leanh::LeanObject,
    mut v_x_4642_: *mut crate::leanh::LeanObject,
    mut v_h__1_4643_: *mut crate::leanh::LeanObject,
    mut v_h__2_4644_: *mut crate::leanh::LeanObject,
    mut v_h__3_4645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4642_) == 0 {
        let mut v_l_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4643_);
        v_l_4646_ = crate::leanh::lean_ctor_get(v_x_4642_, 3);
        if crate::leanh::lean_obj_tag(v_l_4646_) == 0 {
            let mut v_size_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4646_);
            crate::leanh::lean_dec(v_h__2_4644_);
            v_size_4647_ = crate::leanh::lean_ctor_get(v_x_4642_, 0);
            crate::leanh::lean_inc(v_size_4647_);
            v_k_4648_ = crate::leanh::lean_ctor_get(v_x_4642_, 1);
            crate::leanh::lean_inc(v_k_4648_);
            v_v_4649_ = crate::leanh::lean_ctor_get(v_x_4642_, 2);
            crate::leanh::lean_inc(v_v_4649_);
            v_r_4650_ = crate::leanh::lean_ctor_get(v_x_4642_, 4);
            crate::leanh::lean_inc(v_r_4650_);
            crate::leanh::lean_dec_ref_known(v_x_4642_, 5);
            v_size_4651_ = crate::leanh::lean_ctor_get(v_l_4646_, 0);
            crate::leanh::lean_inc(v_size_4651_);
            v_k_4652_ = crate::leanh::lean_ctor_get(v_l_4646_, 1);
            crate::leanh::lean_inc(v_k_4652_);
            v_v_4653_ = crate::leanh::lean_ctor_get(v_l_4646_, 2);
            crate::leanh::lean_inc(v_v_4653_);
            v_l_4654_ = crate::leanh::lean_ctor_get(v_l_4646_, 3);
            crate::leanh::lean_inc(v_l_4654_);
            v_r_4655_ = crate::leanh::lean_ctor_get(v_l_4646_, 4);
            crate::leanh::lean_inc(v_r_4655_);
            crate::leanh::lean_dec_ref_known(v_l_4646_, 5);
            v___x_4656_ = crate::leanh::lean_apply_9(
                v_h__3_4645_,
                v_size_4647_,
                v_k_4648_,
                v_v_4649_,
                v_size_4651_,
                v_k_4652_,
                v_v_4653_,
                v_l_4654_,
                v_r_4655_,
                v_r_4650_,
            );
            return v___x_4656_;
        } else {
            let mut v_size_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4645_);
            v_size_4657_ = crate::leanh::lean_ctor_get(v_x_4642_, 0);
            crate::leanh::lean_inc(v_size_4657_);
            v_k_4658_ = crate::leanh::lean_ctor_get(v_x_4642_, 1);
            crate::leanh::lean_inc(v_k_4658_);
            v_v_4659_ = crate::leanh::lean_ctor_get(v_x_4642_, 2);
            crate::leanh::lean_inc(v_v_4659_);
            v_r_4660_ = crate::leanh::lean_ctor_get(v_x_4642_, 4);
            crate::leanh::lean_inc(v_r_4660_);
            crate::leanh::lean_dec_ref_known(v_x_4642_, 5);
            v___x_4661_ = crate::leanh::lean_apply_4(
                v_h__2_4644_,
                v_size_4657_,
                v_k_4658_,
                v_v_4659_,
                v_r_4660_,
            );
            return v___x_4661_;
        }
    } else {
        let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4645_);
        crate::leanh::lean_dec(v_h__2_4644_);
        v___x_4662_ = crate::leanh::lean_box(0);
        v___x_4663_ = crate::leanh::lean_apply_1(v_h__1_4643_, v___x_4662_);
        return v___x_4663_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(
    mut v_x_4664_: *mut crate::leanh::LeanObject,
    mut v_x_4665_: *mut crate::leanh::LeanObject,
    mut v_h__1_4666_: *mut crate::leanh::LeanObject,
    mut v_h__2_4667_: *mut crate::leanh::LeanObject,
    mut v_h__3_4668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4664_) == 0 {
        let mut v_l_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4666_);
        v_l_4669_ = crate::leanh::lean_ctor_get(v_x_4664_, 3);
        if crate::leanh::lean_obj_tag(v_l_4669_) == 0 {
            let mut v_size_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4669_);
            crate::leanh::lean_dec(v_h__2_4667_);
            v_size_4670_ = crate::leanh::lean_ctor_get(v_x_4664_, 0);
            crate::leanh::lean_inc(v_size_4670_);
            v_k_4671_ = crate::leanh::lean_ctor_get(v_x_4664_, 1);
            crate::leanh::lean_inc(v_k_4671_);
            v_v_4672_ = crate::leanh::lean_ctor_get(v_x_4664_, 2);
            crate::leanh::lean_inc(v_v_4672_);
            v_r_4673_ = crate::leanh::lean_ctor_get(v_x_4664_, 4);
            crate::leanh::lean_inc(v_r_4673_);
            crate::leanh::lean_dec_ref_known(v_x_4664_, 5);
            v_size_4674_ = crate::leanh::lean_ctor_get(v_l_4669_, 0);
            crate::leanh::lean_inc(v_size_4674_);
            v_k_4675_ = crate::leanh::lean_ctor_get(v_l_4669_, 1);
            crate::leanh::lean_inc(v_k_4675_);
            v_v_4676_ = crate::leanh::lean_ctor_get(v_l_4669_, 2);
            crate::leanh::lean_inc(v_v_4676_);
            v_l_4677_ = crate::leanh::lean_ctor_get(v_l_4669_, 3);
            crate::leanh::lean_inc(v_l_4677_);
            v_r_4678_ = crate::leanh::lean_ctor_get(v_l_4669_, 4);
            crate::leanh::lean_inc(v_r_4678_);
            crate::leanh::lean_dec_ref_known(v_l_4669_, 5);
            v___x_4679_ = crate::leanh::lean_apply_10(
                v_h__3_4668_,
                v_size_4670_,
                v_k_4671_,
                v_v_4672_,
                v_size_4674_,
                v_k_4675_,
                v_v_4676_,
                v_l_4677_,
                v_r_4678_,
                v_r_4673_,
                v_x_4665_,
            );
            return v___x_4679_;
        } else {
            let mut v_size_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4668_);
            v_size_4680_ = crate::leanh::lean_ctor_get(v_x_4664_, 0);
            crate::leanh::lean_inc(v_size_4680_);
            v_k_4681_ = crate::leanh::lean_ctor_get(v_x_4664_, 1);
            crate::leanh::lean_inc(v_k_4681_);
            v_v_4682_ = crate::leanh::lean_ctor_get(v_x_4664_, 2);
            crate::leanh::lean_inc(v_v_4682_);
            v_r_4683_ = crate::leanh::lean_ctor_get(v_x_4664_, 4);
            crate::leanh::lean_inc(v_r_4683_);
            crate::leanh::lean_dec_ref_known(v_x_4664_, 5);
            v___x_4684_ = crate::leanh::lean_apply_5(
                v_h__2_4667_,
                v_size_4680_,
                v_k_4681_,
                v_v_4682_,
                v_r_4683_,
                v_x_4665_,
            );
            return v___x_4684_;
        }
    } else {
        let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4668_);
        crate::leanh::lean_dec(v_h__2_4667_);
        v___x_4685_ = crate::leanh::lean_apply_1(v_h__1_4666_, v_x_4665_);
        return v___x_4685_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(
    mut v_00_u03b1_4686_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4687_: *mut crate::leanh::LeanObject,
    mut v_motive_4688_: *mut crate::leanh::LeanObject,
    mut v_x_4689_: *mut crate::leanh::LeanObject,
    mut v_x_4690_: *mut crate::leanh::LeanObject,
    mut v_h__1_4691_: *mut crate::leanh::LeanObject,
    mut v_h__2_4692_: *mut crate::leanh::LeanObject,
    mut v_h__3_4693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4689_) == 0 {
        let mut v_l_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4691_);
        v_l_4694_ = crate::leanh::lean_ctor_get(v_x_4689_, 3);
        if crate::leanh::lean_obj_tag(v_l_4694_) == 0 {
            let mut v_size_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_4694_);
            crate::leanh::lean_dec(v_h__2_4692_);
            v_size_4695_ = crate::leanh::lean_ctor_get(v_x_4689_, 0);
            crate::leanh::lean_inc(v_size_4695_);
            v_k_4696_ = crate::leanh::lean_ctor_get(v_x_4689_, 1);
            crate::leanh::lean_inc(v_k_4696_);
            v_v_4697_ = crate::leanh::lean_ctor_get(v_x_4689_, 2);
            crate::leanh::lean_inc(v_v_4697_);
            v_r_4698_ = crate::leanh::lean_ctor_get(v_x_4689_, 4);
            crate::leanh::lean_inc(v_r_4698_);
            crate::leanh::lean_dec_ref_known(v_x_4689_, 5);
            v_size_4699_ = crate::leanh::lean_ctor_get(v_l_4694_, 0);
            crate::leanh::lean_inc(v_size_4699_);
            v_k_4700_ = crate::leanh::lean_ctor_get(v_l_4694_, 1);
            crate::leanh::lean_inc(v_k_4700_);
            v_v_4701_ = crate::leanh::lean_ctor_get(v_l_4694_, 2);
            crate::leanh::lean_inc(v_v_4701_);
            v_l_4702_ = crate::leanh::lean_ctor_get(v_l_4694_, 3);
            crate::leanh::lean_inc(v_l_4702_);
            v_r_4703_ = crate::leanh::lean_ctor_get(v_l_4694_, 4);
            crate::leanh::lean_inc(v_r_4703_);
            crate::leanh::lean_dec_ref_known(v_l_4694_, 5);
            v___x_4704_ = crate::leanh::lean_apply_10(
                v_h__3_4693_,
                v_size_4695_,
                v_k_4696_,
                v_v_4697_,
                v_size_4699_,
                v_k_4700_,
                v_v_4701_,
                v_l_4702_,
                v_r_4703_,
                v_r_4698_,
                v_x_4690_,
            );
            return v___x_4704_;
        } else {
            let mut v_size_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4693_);
            v_size_4705_ = crate::leanh::lean_ctor_get(v_x_4689_, 0);
            crate::leanh::lean_inc(v_size_4705_);
            v_k_4706_ = crate::leanh::lean_ctor_get(v_x_4689_, 1);
            crate::leanh::lean_inc(v_k_4706_);
            v_v_4707_ = crate::leanh::lean_ctor_get(v_x_4689_, 2);
            crate::leanh::lean_inc(v_v_4707_);
            v_r_4708_ = crate::leanh::lean_ctor_get(v_x_4689_, 4);
            crate::leanh::lean_inc(v_r_4708_);
            crate::leanh::lean_dec_ref_known(v_x_4689_, 5);
            v___x_4709_ = crate::leanh::lean_apply_5(
                v_h__2_4692_,
                v_size_4705_,
                v_k_4706_,
                v_v_4707_,
                v_r_4708_,
                v_x_4690_,
            );
            return v___x_4709_;
        }
    } else {
        let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4693_);
        crate::leanh::lean_dec(v_h__2_4692_);
        v___x_4710_ = crate::leanh::lean_apply_1(v_h__1_4691_, v_x_4690_);
        return v___x_4710_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(
    mut v_x_4711_: *mut crate::leanh::LeanObject,
    mut v_h__1_4712_: *mut crate::leanh::LeanObject,
    mut v_h__2_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_4714_ = crate::leanh::lean_ctor_get(v_x_4711_, 3);
    if crate::leanh::lean_obj_tag(v_l_4714_) == 0 {
        let mut v_size_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_l_4714_);
        crate::leanh::lean_dec(v_h__1_4712_);
        v_size_4715_ = crate::leanh::lean_ctor_get(v_x_4711_, 0);
        crate::leanh::lean_inc(v_size_4715_);
        v_k_4716_ = crate::leanh::lean_ctor_get(v_x_4711_, 1);
        crate::leanh::lean_inc(v_k_4716_);
        v_v_4717_ = crate::leanh::lean_ctor_get(v_x_4711_, 2);
        crate::leanh::lean_inc(v_v_4717_);
        v_r_4718_ = crate::leanh::lean_ctor_get(v_x_4711_, 4);
        crate::leanh::lean_inc(v_r_4718_);
        crate::leanh::lean_dec(v_x_4711_);
        v_size_4719_ = crate::leanh::lean_ctor_get(v_l_4714_, 0);
        crate::leanh::lean_inc(v_size_4719_);
        v_k_4720_ = crate::leanh::lean_ctor_get(v_l_4714_, 1);
        crate::leanh::lean_inc(v_k_4720_);
        v_v_4721_ = crate::leanh::lean_ctor_get(v_l_4714_, 2);
        crate::leanh::lean_inc(v_v_4721_);
        v_l_4722_ = crate::leanh::lean_ctor_get(v_l_4714_, 3);
        crate::leanh::lean_inc(v_l_4722_);
        v_r_4723_ = crate::leanh::lean_ctor_get(v_l_4714_, 4);
        crate::leanh::lean_inc(v_r_4723_);
        crate::leanh::lean_dec_ref_known(v_l_4714_, 5);
        v___x_4724_ = crate::leanh::lean_apply_10(
            v_h__2_4713_,
            v_size_4715_,
            v_k_4716_,
            v_v_4717_,
            v_size_4719_,
            v_k_4720_,
            v_v_4721_,
            v_l_4722_,
            v_r_4723_,
            v_r_4718_,
            crate::leanh::lean_box(0),
        );
        return v___x_4724_;
    } else {
        let mut v_size_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4713_);
        v_size_4725_ = crate::leanh::lean_ctor_get(v_x_4711_, 0);
        crate::leanh::lean_inc(v_size_4725_);
        v_k_4726_ = crate::leanh::lean_ctor_get(v_x_4711_, 1);
        crate::leanh::lean_inc(v_k_4726_);
        v_v_4727_ = crate::leanh::lean_ctor_get(v_x_4711_, 2);
        crate::leanh::lean_inc(v_v_4727_);
        v_r_4728_ = crate::leanh::lean_ctor_get(v_x_4711_, 4);
        crate::leanh::lean_inc(v_r_4728_);
        crate::leanh::lean_dec(v_x_4711_);
        v___x_4729_ = crate::leanh::lean_apply_5(
            v_h__1_4712_,
            v_size_4725_,
            v_k_4726_,
            v_v_4727_,
            v_r_4728_,
            crate::leanh::lean_box(0),
        );
        return v___x_4729_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(
    mut v_00_u03b1_4730_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4731_: *mut crate::leanh::LeanObject,
    mut v_motive_4732_: *mut crate::leanh::LeanObject,
    mut v_x_4733_: *mut crate::leanh::LeanObject,
    mut v_x_4734_: *mut crate::leanh::LeanObject,
    mut v_h__1_4735_: *mut crate::leanh::LeanObject,
    mut v_h__2_4736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_4737_ = crate::leanh::lean_ctor_get(v_x_4733_, 3);
    if crate::leanh::lean_obj_tag(v_l_4737_) == 0 {
        let mut v_size_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_l_4737_);
        crate::leanh::lean_dec(v_h__1_4735_);
        v_size_4738_ = crate::leanh::lean_ctor_get(v_x_4733_, 0);
        crate::leanh::lean_inc(v_size_4738_);
        v_k_4739_ = crate::leanh::lean_ctor_get(v_x_4733_, 1);
        crate::leanh::lean_inc(v_k_4739_);
        v_v_4740_ = crate::leanh::lean_ctor_get(v_x_4733_, 2);
        crate::leanh::lean_inc(v_v_4740_);
        v_r_4741_ = crate::leanh::lean_ctor_get(v_x_4733_, 4);
        crate::leanh::lean_inc(v_r_4741_);
        crate::leanh::lean_dec(v_x_4733_);
        v_size_4742_ = crate::leanh::lean_ctor_get(v_l_4737_, 0);
        crate::leanh::lean_inc(v_size_4742_);
        v_k_4743_ = crate::leanh::lean_ctor_get(v_l_4737_, 1);
        crate::leanh::lean_inc(v_k_4743_);
        v_v_4744_ = crate::leanh::lean_ctor_get(v_l_4737_, 2);
        crate::leanh::lean_inc(v_v_4744_);
        v_l_4745_ = crate::leanh::lean_ctor_get(v_l_4737_, 3);
        crate::leanh::lean_inc(v_l_4745_);
        v_r_4746_ = crate::leanh::lean_ctor_get(v_l_4737_, 4);
        crate::leanh::lean_inc(v_r_4746_);
        crate::leanh::lean_dec_ref_known(v_l_4737_, 5);
        v___x_4747_ = crate::leanh::lean_apply_10(
            v_h__2_4736_,
            v_size_4738_,
            v_k_4739_,
            v_v_4740_,
            v_size_4742_,
            v_k_4743_,
            v_v_4744_,
            v_l_4745_,
            v_r_4746_,
            v_r_4741_,
            crate::leanh::lean_box(0),
        );
        return v___x_4747_;
    } else {
        let mut v_size_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4736_);
        v_size_4748_ = crate::leanh::lean_ctor_get(v_x_4733_, 0);
        crate::leanh::lean_inc(v_size_4748_);
        v_k_4749_ = crate::leanh::lean_ctor_get(v_x_4733_, 1);
        crate::leanh::lean_inc(v_k_4749_);
        v_v_4750_ = crate::leanh::lean_ctor_get(v_x_4733_, 2);
        crate::leanh::lean_inc(v_v_4750_);
        v_r_4751_ = crate::leanh::lean_ctor_get(v_x_4733_, 4);
        crate::leanh::lean_inc(v_r_4751_);
        crate::leanh::lean_dec(v_x_4733_);
        v___x_4752_ = crate::leanh::lean_apply_5(
            v_h__1_4735_,
            v_size_4748_,
            v_k_4749_,
            v_v_4750_,
            v_r_4751_,
            crate::leanh::lean_box(0),
        );
        return v___x_4752_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(
    mut v_x_4753_: *mut crate::leanh::LeanObject,
    mut v_h__1_4754_: *mut crate::leanh::LeanObject,
    mut v_h__2_4755_: *mut crate::leanh::LeanObject,
    mut v_h__3_4756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4753_) == 0 {
        let mut v_r_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4754_);
        v_r_4757_ = crate::leanh::lean_ctor_get(v_x_4753_, 4);
        if crate::leanh::lean_obj_tag(v_r_4757_) == 0 {
            let mut v_size_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4757_);
            crate::leanh::lean_dec(v_h__2_4755_);
            v_size_4758_ = crate::leanh::lean_ctor_get(v_x_4753_, 0);
            crate::leanh::lean_inc(v_size_4758_);
            v_k_4759_ = crate::leanh::lean_ctor_get(v_x_4753_, 1);
            crate::leanh::lean_inc(v_k_4759_);
            v_v_4760_ = crate::leanh::lean_ctor_get(v_x_4753_, 2);
            crate::leanh::lean_inc(v_v_4760_);
            v_l_4761_ = crate::leanh::lean_ctor_get(v_x_4753_, 3);
            crate::leanh::lean_inc(v_l_4761_);
            crate::leanh::lean_dec_ref_known(v_x_4753_, 5);
            v_size_4762_ = crate::leanh::lean_ctor_get(v_r_4757_, 0);
            crate::leanh::lean_inc(v_size_4762_);
            v_k_4763_ = crate::leanh::lean_ctor_get(v_r_4757_, 1);
            crate::leanh::lean_inc(v_k_4763_);
            v_v_4764_ = crate::leanh::lean_ctor_get(v_r_4757_, 2);
            crate::leanh::lean_inc(v_v_4764_);
            v_l_4765_ = crate::leanh::lean_ctor_get(v_r_4757_, 3);
            crate::leanh::lean_inc(v_l_4765_);
            v_r_4766_ = crate::leanh::lean_ctor_get(v_r_4757_, 4);
            crate::leanh::lean_inc(v_r_4766_);
            crate::leanh::lean_dec_ref_known(v_r_4757_, 5);
            v___x_4767_ = crate::leanh::lean_apply_9(
                v_h__3_4756_,
                v_size_4758_,
                v_k_4759_,
                v_v_4760_,
                v_l_4761_,
                v_size_4762_,
                v_k_4763_,
                v_v_4764_,
                v_l_4765_,
                v_r_4766_,
            );
            return v___x_4767_;
        } else {
            let mut v_size_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4756_);
            v_size_4768_ = crate::leanh::lean_ctor_get(v_x_4753_, 0);
            crate::leanh::lean_inc(v_size_4768_);
            v_k_4769_ = crate::leanh::lean_ctor_get(v_x_4753_, 1);
            crate::leanh::lean_inc(v_k_4769_);
            v_v_4770_ = crate::leanh::lean_ctor_get(v_x_4753_, 2);
            crate::leanh::lean_inc(v_v_4770_);
            v_l_4771_ = crate::leanh::lean_ctor_get(v_x_4753_, 3);
            crate::leanh::lean_inc(v_l_4771_);
            crate::leanh::lean_dec_ref_known(v_x_4753_, 5);
            v___x_4772_ = crate::leanh::lean_apply_4(
                v_h__2_4755_,
                v_size_4768_,
                v_k_4769_,
                v_v_4770_,
                v_l_4771_,
            );
            return v___x_4772_;
        }
    } else {
        let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4756_);
        crate::leanh::lean_dec(v_h__2_4755_);
        v___x_4773_ = crate::leanh::lean_box(0);
        v___x_4774_ = crate::leanh::lean_apply_1(v_h__1_4754_, v___x_4773_);
        return v___x_4774_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4775_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4776_: *mut crate::leanh::LeanObject,
    mut v_motive_4777_: *mut crate::leanh::LeanObject,
    mut v_x_4778_: *mut crate::leanh::LeanObject,
    mut v_h__1_4779_: *mut crate::leanh::LeanObject,
    mut v_h__2_4780_: *mut crate::leanh::LeanObject,
    mut v_h__3_4781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4778_) == 0 {
        let mut v_r_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4779_);
        v_r_4782_ = crate::leanh::lean_ctor_get(v_x_4778_, 4);
        if crate::leanh::lean_obj_tag(v_r_4782_) == 0 {
            let mut v_size_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4782_);
            crate::leanh::lean_dec(v_h__2_4780_);
            v_size_4783_ = crate::leanh::lean_ctor_get(v_x_4778_, 0);
            crate::leanh::lean_inc(v_size_4783_);
            v_k_4784_ = crate::leanh::lean_ctor_get(v_x_4778_, 1);
            crate::leanh::lean_inc(v_k_4784_);
            v_v_4785_ = crate::leanh::lean_ctor_get(v_x_4778_, 2);
            crate::leanh::lean_inc(v_v_4785_);
            v_l_4786_ = crate::leanh::lean_ctor_get(v_x_4778_, 3);
            crate::leanh::lean_inc(v_l_4786_);
            crate::leanh::lean_dec_ref_known(v_x_4778_, 5);
            v_size_4787_ = crate::leanh::lean_ctor_get(v_r_4782_, 0);
            crate::leanh::lean_inc(v_size_4787_);
            v_k_4788_ = crate::leanh::lean_ctor_get(v_r_4782_, 1);
            crate::leanh::lean_inc(v_k_4788_);
            v_v_4789_ = crate::leanh::lean_ctor_get(v_r_4782_, 2);
            crate::leanh::lean_inc(v_v_4789_);
            v_l_4790_ = crate::leanh::lean_ctor_get(v_r_4782_, 3);
            crate::leanh::lean_inc(v_l_4790_);
            v_r_4791_ = crate::leanh::lean_ctor_get(v_r_4782_, 4);
            crate::leanh::lean_inc(v_r_4791_);
            crate::leanh::lean_dec_ref_known(v_r_4782_, 5);
            v___x_4792_ = crate::leanh::lean_apply_9(
                v_h__3_4781_,
                v_size_4783_,
                v_k_4784_,
                v_v_4785_,
                v_l_4786_,
                v_size_4787_,
                v_k_4788_,
                v_v_4789_,
                v_l_4790_,
                v_r_4791_,
            );
            return v___x_4792_;
        } else {
            let mut v_size_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4781_);
            v_size_4793_ = crate::leanh::lean_ctor_get(v_x_4778_, 0);
            crate::leanh::lean_inc(v_size_4793_);
            v_k_4794_ = crate::leanh::lean_ctor_get(v_x_4778_, 1);
            crate::leanh::lean_inc(v_k_4794_);
            v_v_4795_ = crate::leanh::lean_ctor_get(v_x_4778_, 2);
            crate::leanh::lean_inc(v_v_4795_);
            v_l_4796_ = crate::leanh::lean_ctor_get(v_x_4778_, 3);
            crate::leanh::lean_inc(v_l_4796_);
            crate::leanh::lean_dec_ref_known(v_x_4778_, 5);
            v___x_4797_ = crate::leanh::lean_apply_4(
                v_h__2_4780_,
                v_size_4793_,
                v_k_4794_,
                v_v_4795_,
                v_l_4796_,
            );
            return v___x_4797_;
        }
    } else {
        let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4781_);
        crate::leanh::lean_dec(v_h__2_4780_);
        v___x_4798_ = crate::leanh::lean_box(0);
        v___x_4799_ = crate::leanh::lean_apply_1(v_h__1_4779_, v___x_4798_);
        return v___x_4799_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(
    mut v_x_4800_: *mut crate::leanh::LeanObject,
    mut v_x_4801_: *mut crate::leanh::LeanObject,
    mut v_h__1_4802_: *mut crate::leanh::LeanObject,
    mut v_h__2_4803_: *mut crate::leanh::LeanObject,
    mut v_h__3_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4800_) == 0 {
        let mut v_r_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4802_);
        v_r_4805_ = crate::leanh::lean_ctor_get(v_x_4800_, 4);
        if crate::leanh::lean_obj_tag(v_r_4805_) == 0 {
            let mut v_size_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4805_);
            crate::leanh::lean_dec(v_h__2_4803_);
            v_size_4806_ = crate::leanh::lean_ctor_get(v_x_4800_, 0);
            crate::leanh::lean_inc(v_size_4806_);
            v_k_4807_ = crate::leanh::lean_ctor_get(v_x_4800_, 1);
            crate::leanh::lean_inc(v_k_4807_);
            v_v_4808_ = crate::leanh::lean_ctor_get(v_x_4800_, 2);
            crate::leanh::lean_inc(v_v_4808_);
            v_l_4809_ = crate::leanh::lean_ctor_get(v_x_4800_, 3);
            crate::leanh::lean_inc(v_l_4809_);
            crate::leanh::lean_dec_ref_known(v_x_4800_, 5);
            v_size_4810_ = crate::leanh::lean_ctor_get(v_r_4805_, 0);
            crate::leanh::lean_inc(v_size_4810_);
            v_k_4811_ = crate::leanh::lean_ctor_get(v_r_4805_, 1);
            crate::leanh::lean_inc(v_k_4811_);
            v_v_4812_ = crate::leanh::lean_ctor_get(v_r_4805_, 2);
            crate::leanh::lean_inc(v_v_4812_);
            v_l_4813_ = crate::leanh::lean_ctor_get(v_r_4805_, 3);
            crate::leanh::lean_inc(v_l_4813_);
            v_r_4814_ = crate::leanh::lean_ctor_get(v_r_4805_, 4);
            crate::leanh::lean_inc(v_r_4814_);
            crate::leanh::lean_dec_ref_known(v_r_4805_, 5);
            v___x_4815_ = crate::leanh::lean_apply_10(
                v_h__3_4804_,
                v_size_4806_,
                v_k_4807_,
                v_v_4808_,
                v_l_4809_,
                v_size_4810_,
                v_k_4811_,
                v_v_4812_,
                v_l_4813_,
                v_r_4814_,
                v_x_4801_,
            );
            return v___x_4815_;
        } else {
            let mut v_size_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4804_);
            v_size_4816_ = crate::leanh::lean_ctor_get(v_x_4800_, 0);
            crate::leanh::lean_inc(v_size_4816_);
            v_k_4817_ = crate::leanh::lean_ctor_get(v_x_4800_, 1);
            crate::leanh::lean_inc(v_k_4817_);
            v_v_4818_ = crate::leanh::lean_ctor_get(v_x_4800_, 2);
            crate::leanh::lean_inc(v_v_4818_);
            v_l_4819_ = crate::leanh::lean_ctor_get(v_x_4800_, 3);
            crate::leanh::lean_inc(v_l_4819_);
            crate::leanh::lean_dec_ref_known(v_x_4800_, 5);
            v___x_4820_ = crate::leanh::lean_apply_5(
                v_h__2_4803_,
                v_size_4816_,
                v_k_4817_,
                v_v_4818_,
                v_l_4819_,
                v_x_4801_,
            );
            return v___x_4820_;
        }
    } else {
        let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4804_);
        crate::leanh::lean_dec(v_h__2_4803_);
        v___x_4821_ = crate::leanh::lean_apply_1(v_h__1_4802_, v_x_4801_);
        return v___x_4821_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(
    mut v_00_u03b1_4822_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4823_: *mut crate::leanh::LeanObject,
    mut v_motive_4824_: *mut crate::leanh::LeanObject,
    mut v_x_4825_: *mut crate::leanh::LeanObject,
    mut v_x_4826_: *mut crate::leanh::LeanObject,
    mut v_h__1_4827_: *mut crate::leanh::LeanObject,
    mut v_h__2_4828_: *mut crate::leanh::LeanObject,
    mut v_h__3_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4825_) == 0 {
        let mut v_r_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4827_);
        v_r_4830_ = crate::leanh::lean_ctor_get(v_x_4825_, 4);
        if crate::leanh::lean_obj_tag(v_r_4830_) == 0 {
            let mut v_size_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_4830_);
            crate::leanh::lean_dec(v_h__2_4828_);
            v_size_4831_ = crate::leanh::lean_ctor_get(v_x_4825_, 0);
            crate::leanh::lean_inc(v_size_4831_);
            v_k_4832_ = crate::leanh::lean_ctor_get(v_x_4825_, 1);
            crate::leanh::lean_inc(v_k_4832_);
            v_v_4833_ = crate::leanh::lean_ctor_get(v_x_4825_, 2);
            crate::leanh::lean_inc(v_v_4833_);
            v_l_4834_ = crate::leanh::lean_ctor_get(v_x_4825_, 3);
            crate::leanh::lean_inc(v_l_4834_);
            crate::leanh::lean_dec_ref_known(v_x_4825_, 5);
            v_size_4835_ = crate::leanh::lean_ctor_get(v_r_4830_, 0);
            crate::leanh::lean_inc(v_size_4835_);
            v_k_4836_ = crate::leanh::lean_ctor_get(v_r_4830_, 1);
            crate::leanh::lean_inc(v_k_4836_);
            v_v_4837_ = crate::leanh::lean_ctor_get(v_r_4830_, 2);
            crate::leanh::lean_inc(v_v_4837_);
            v_l_4838_ = crate::leanh::lean_ctor_get(v_r_4830_, 3);
            crate::leanh::lean_inc(v_l_4838_);
            v_r_4839_ = crate::leanh::lean_ctor_get(v_r_4830_, 4);
            crate::leanh::lean_inc(v_r_4839_);
            crate::leanh::lean_dec_ref_known(v_r_4830_, 5);
            v___x_4840_ = crate::leanh::lean_apply_10(
                v_h__3_4829_,
                v_size_4831_,
                v_k_4832_,
                v_v_4833_,
                v_l_4834_,
                v_size_4835_,
                v_k_4836_,
                v_v_4837_,
                v_l_4838_,
                v_r_4839_,
                v_x_4826_,
            );
            return v___x_4840_;
        } else {
            let mut v_size_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4829_);
            v_size_4841_ = crate::leanh::lean_ctor_get(v_x_4825_, 0);
            crate::leanh::lean_inc(v_size_4841_);
            v_k_4842_ = crate::leanh::lean_ctor_get(v_x_4825_, 1);
            crate::leanh::lean_inc(v_k_4842_);
            v_v_4843_ = crate::leanh::lean_ctor_get(v_x_4825_, 2);
            crate::leanh::lean_inc(v_v_4843_);
            v_l_4844_ = crate::leanh::lean_ctor_get(v_x_4825_, 3);
            crate::leanh::lean_inc(v_l_4844_);
            crate::leanh::lean_dec_ref_known(v_x_4825_, 5);
            v___x_4845_ = crate::leanh::lean_apply_5(
                v_h__2_4828_,
                v_size_4841_,
                v_k_4842_,
                v_v_4843_,
                v_l_4844_,
                v_x_4826_,
            );
            return v___x_4845_;
        }
    } else {
        let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4829_);
        crate::leanh::lean_dec(v_h__2_4828_);
        v___x_4846_ = crate::leanh::lean_apply_1(v_h__1_4827_, v_x_4826_);
        return v___x_4846_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(
    mut v_x_4847_: *mut crate::leanh::LeanObject,
    mut v_h__1_4848_: *mut crate::leanh::LeanObject,
    mut v_h__2_4849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_4850_ = crate::leanh::lean_ctor_get(v_x_4847_, 4);
    if crate::leanh::lean_obj_tag(v_r_4850_) == 0 {
        let mut v_size_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_r_4850_);
        crate::leanh::lean_dec(v_h__1_4848_);
        v_size_4851_ = crate::leanh::lean_ctor_get(v_x_4847_, 0);
        crate::leanh::lean_inc(v_size_4851_);
        v_k_4852_ = crate::leanh::lean_ctor_get(v_x_4847_, 1);
        crate::leanh::lean_inc(v_k_4852_);
        v_v_4853_ = crate::leanh::lean_ctor_get(v_x_4847_, 2);
        crate::leanh::lean_inc(v_v_4853_);
        v_l_4854_ = crate::leanh::lean_ctor_get(v_x_4847_, 3);
        crate::leanh::lean_inc(v_l_4854_);
        crate::leanh::lean_dec(v_x_4847_);
        v_size_4855_ = crate::leanh::lean_ctor_get(v_r_4850_, 0);
        crate::leanh::lean_inc(v_size_4855_);
        v_k_4856_ = crate::leanh::lean_ctor_get(v_r_4850_, 1);
        crate::leanh::lean_inc(v_k_4856_);
        v_v_4857_ = crate::leanh::lean_ctor_get(v_r_4850_, 2);
        crate::leanh::lean_inc(v_v_4857_);
        v_l_4858_ = crate::leanh::lean_ctor_get(v_r_4850_, 3);
        crate::leanh::lean_inc(v_l_4858_);
        v_r_4859_ = crate::leanh::lean_ctor_get(v_r_4850_, 4);
        crate::leanh::lean_inc(v_r_4859_);
        crate::leanh::lean_dec_ref_known(v_r_4850_, 5);
        v___x_4860_ = crate::leanh::lean_apply_10(
            v_h__2_4849_,
            v_size_4851_,
            v_k_4852_,
            v_v_4853_,
            v_l_4854_,
            v_size_4855_,
            v_k_4856_,
            v_v_4857_,
            v_l_4858_,
            v_r_4859_,
            crate::leanh::lean_box(0),
        );
        return v___x_4860_;
    } else {
        let mut v_size_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4849_);
        v_size_4861_ = crate::leanh::lean_ctor_get(v_x_4847_, 0);
        crate::leanh::lean_inc(v_size_4861_);
        v_k_4862_ = crate::leanh::lean_ctor_get(v_x_4847_, 1);
        crate::leanh::lean_inc(v_k_4862_);
        v_v_4863_ = crate::leanh::lean_ctor_get(v_x_4847_, 2);
        crate::leanh::lean_inc(v_v_4863_);
        v_l_4864_ = crate::leanh::lean_ctor_get(v_x_4847_, 3);
        crate::leanh::lean_inc(v_l_4864_);
        crate::leanh::lean_dec(v_x_4847_);
        v___x_4865_ = crate::leanh::lean_apply_5(
            v_h__1_4848_,
            v_size_4861_,
            v_k_4862_,
            v_v_4863_,
            v_l_4864_,
            crate::leanh::lean_box(0),
        );
        return v___x_4865_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(
    mut v_00_u03b1_4866_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4867_: *mut crate::leanh::LeanObject,
    mut v_motive_4868_: *mut crate::leanh::LeanObject,
    mut v_x_4869_: *mut crate::leanh::LeanObject,
    mut v_x_4870_: *mut crate::leanh::LeanObject,
    mut v_h__1_4871_: *mut crate::leanh::LeanObject,
    mut v_h__2_4872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_4873_ = crate::leanh::lean_ctor_get(v_x_4869_, 4);
    if crate::leanh::lean_obj_tag(v_r_4873_) == 0 {
        let mut v_size_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_r_4873_);
        crate::leanh::lean_dec(v_h__1_4871_);
        v_size_4874_ = crate::leanh::lean_ctor_get(v_x_4869_, 0);
        crate::leanh::lean_inc(v_size_4874_);
        v_k_4875_ = crate::leanh::lean_ctor_get(v_x_4869_, 1);
        crate::leanh::lean_inc(v_k_4875_);
        v_v_4876_ = crate::leanh::lean_ctor_get(v_x_4869_, 2);
        crate::leanh::lean_inc(v_v_4876_);
        v_l_4877_ = crate::leanh::lean_ctor_get(v_x_4869_, 3);
        crate::leanh::lean_inc(v_l_4877_);
        crate::leanh::lean_dec(v_x_4869_);
        v_size_4878_ = crate::leanh::lean_ctor_get(v_r_4873_, 0);
        crate::leanh::lean_inc(v_size_4878_);
        v_k_4879_ = crate::leanh::lean_ctor_get(v_r_4873_, 1);
        crate::leanh::lean_inc(v_k_4879_);
        v_v_4880_ = crate::leanh::lean_ctor_get(v_r_4873_, 2);
        crate::leanh::lean_inc(v_v_4880_);
        v_l_4881_ = crate::leanh::lean_ctor_get(v_r_4873_, 3);
        crate::leanh::lean_inc(v_l_4881_);
        v_r_4882_ = crate::leanh::lean_ctor_get(v_r_4873_, 4);
        crate::leanh::lean_inc(v_r_4882_);
        crate::leanh::lean_dec_ref_known(v_r_4873_, 5);
        v___x_4883_ = crate::leanh::lean_apply_10(
            v_h__2_4872_,
            v_size_4874_,
            v_k_4875_,
            v_v_4876_,
            v_l_4877_,
            v_size_4878_,
            v_k_4879_,
            v_v_4880_,
            v_l_4881_,
            v_r_4882_,
            crate::leanh::lean_box(0),
        );
        return v___x_4883_;
    } else {
        let mut v_size_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4872_);
        v_size_4884_ = crate::leanh::lean_ctor_get(v_x_4869_, 0);
        crate::leanh::lean_inc(v_size_4884_);
        v_k_4885_ = crate::leanh::lean_ctor_get(v_x_4869_, 1);
        crate::leanh::lean_inc(v_k_4885_);
        v_v_4886_ = crate::leanh::lean_ctor_get(v_x_4869_, 2);
        crate::leanh::lean_inc(v_v_4886_);
        v_l_4887_ = crate::leanh::lean_ctor_get(v_x_4869_, 3);
        crate::leanh::lean_inc(v_l_4887_);
        crate::leanh::lean_dec(v_x_4869_);
        v___x_4888_ = crate::leanh::lean_apply_5(
            v_h__1_4871_,
            v_size_4884_,
            v_k_4885_,
            v_v_4886_,
            v_l_4887_,
            crate::leanh::lean_box(0),
        );
        return v___x_4888_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(
    mut v_l_4889_: *mut crate::leanh::LeanObject,
    mut v_h__1_4890_: *mut crate::leanh::LeanObject,
    mut v_h__2_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_4889_) == 0 {
        let mut v_size_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4890_);
        v_size_4892_ = crate::leanh::lean_ctor_get(v_l_4889_, 0);
        crate::leanh::lean_inc(v_size_4892_);
        v_k_4893_ = crate::leanh::lean_ctor_get(v_l_4889_, 1);
        crate::leanh::lean_inc(v_k_4893_);
        v_v_4894_ = crate::leanh::lean_ctor_get(v_l_4889_, 2);
        crate::leanh::lean_inc(v_v_4894_);
        v_l_4895_ = crate::leanh::lean_ctor_get(v_l_4889_, 3);
        crate::leanh::lean_inc(v_l_4895_);
        v_r_4896_ = crate::leanh::lean_ctor_get(v_l_4889_, 4);
        crate::leanh::lean_inc(v_r_4896_);
        crate::leanh::lean_dec_ref_known(v_l_4889_, 5);
        v___x_4897_ = crate::leanh::lean_apply_7(
            v_h__2_4891_,
            v_size_4892_,
            v_k_4893_,
            v_v_4894_,
            v_l_4895_,
            v_r_4896_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_4897_;
    } else {
        let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4891_);
        v___x_4898_ = crate::leanh::lean_apply_2(
            v_h__1_4890_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_4898_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(
    mut v_00_u03b1_4899_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4900_: *mut crate::leanh::LeanObject,
    mut v_r_4901_: *mut crate::leanh::LeanObject,
    mut v_motive_4902_: *mut crate::leanh::LeanObject,
    mut v_l_4903_: *mut crate::leanh::LeanObject,
    mut v_hl_4904_: *mut crate::leanh::LeanObject,
    mut v_hlr_4905_: *mut crate::leanh::LeanObject,
    mut v_h__1_4906_: *mut crate::leanh::LeanObject,
    mut v_h__2_4907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_4903_) == 0 {
        let mut v_size_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4906_);
        v_size_4908_ = crate::leanh::lean_ctor_get(v_l_4903_, 0);
        crate::leanh::lean_inc(v_size_4908_);
        v_k_4909_ = crate::leanh::lean_ctor_get(v_l_4903_, 1);
        crate::leanh::lean_inc(v_k_4909_);
        v_v_4910_ = crate::leanh::lean_ctor_get(v_l_4903_, 2);
        crate::leanh::lean_inc(v_v_4910_);
        v_l_4911_ = crate::leanh::lean_ctor_get(v_l_4903_, 3);
        crate::leanh::lean_inc(v_l_4911_);
        v_r_4912_ = crate::leanh::lean_ctor_get(v_l_4903_, 4);
        crate::leanh::lean_inc(v_r_4912_);
        crate::leanh::lean_dec_ref_known(v_l_4903_, 5);
        v___x_4913_ = crate::leanh::lean_apply_7(
            v_h__2_4907_,
            v_size_4908_,
            v_k_4909_,
            v_v_4910_,
            v_l_4911_,
            v_r_4912_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_4913_;
    } else {
        let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4907_);
        v___x_4914_ = crate::leanh::lean_apply_2(
            v_h__1_4906_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_4914_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(
    mut v_00_u03b1_4915_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4916_: *mut crate::leanh::LeanObject,
    mut v_r_4917_: *mut crate::leanh::LeanObject,
    mut v_motive_4918_: *mut crate::leanh::LeanObject,
    mut v_l_4919_: *mut crate::leanh::LeanObject,
    mut v_hl_4920_: *mut crate::leanh::LeanObject,
    mut v_hlr_4921_: *mut crate::leanh::LeanObject,
    mut v_h__1_4922_: *mut crate::leanh::LeanObject,
    mut v_h__2_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_4915_, v_00_u03b2_4916_, v_r_4917_, v_motive_4918_, v_l_4919_, v_hl_4920_, v_hlr_4921_, v_h__1_4922_, v_h__2_4923_);
    crate::leanh::lean_dec(v_r_4917_);
    return v_res_4924_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(
    mut v_x_4925_: *mut crate::leanh::LeanObject,
    mut v_h__1_4926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_4927_ = crate::leanh::lean_ctor_get(v_x_4925_, 0);
    crate::leanh::lean_inc(v_k_4927_);
    v_v_4928_ = crate::leanh::lean_ctor_get(v_x_4925_, 1);
    crate::leanh::lean_inc(v_v_4928_);
    v_tree_4929_ = crate::leanh::lean_ctor_get(v_x_4925_, 2);
    crate::leanh::lean_inc(v_tree_4929_);
    crate::leanh::lean_dec_ref(v_x_4925_);
    v___x_4930_ = crate::leanh::lean_apply_5(
        v_h__1_4926_,
        v_k_4927_,
        v_v_4928_,
        v_tree_4929_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4930_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(
    mut v_00_u03b1_4931_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4932_: *mut crate::leanh::LeanObject,
    mut v_l_x27_4933_: *mut crate::leanh::LeanObject,
    mut v_r_x27_4934_: *mut crate::leanh::LeanObject,
    mut v_motive_4935_: *mut crate::leanh::LeanObject,
    mut v_x_4936_: *mut crate::leanh::LeanObject,
    mut v_h__1_4937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_4938_ = crate::leanh::lean_ctor_get(v_x_4936_, 0);
    crate::leanh::lean_inc(v_k_4938_);
    v_v_4939_ = crate::leanh::lean_ctor_get(v_x_4936_, 1);
    crate::leanh::lean_inc(v_v_4939_);
    v_tree_4940_ = crate::leanh::lean_ctor_get(v_x_4936_, 2);
    crate::leanh::lean_inc(v_tree_4940_);
    crate::leanh::lean_dec_ref(v_x_4936_);
    v___x_4941_ = crate::leanh::lean_apply_5(
        v_h__1_4937_,
        v_k_4938_,
        v_v_4939_,
        v_tree_4940_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4941_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(
    mut v_00_u03b1_4942_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4943_: *mut crate::leanh::LeanObject,
    mut v_l_x27_4944_: *mut crate::leanh::LeanObject,
    mut v_r_x27_4945_: *mut crate::leanh::LeanObject,
    mut v_motive_4946_: *mut crate::leanh::LeanObject,
    mut v_x_4947_: *mut crate::leanh::LeanObject,
    mut v_h__1_4948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4949_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_4942_, v_00_u03b2_4943_, v_l_x27_4944_, v_r_x27_4945_, v_motive_4946_, v_x_4947_, v_h__1_4948_);
    crate::leanh::lean_dec(v_r_x27_4945_);
    crate::leanh::lean_dec(v_l_x27_4944_);
    return v_res_4949_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(
    mut v_l_4950_: *mut crate::leanh::LeanObject,
    mut v_h__1_4951_: *mut crate::leanh::LeanObject,
    mut v_h__2_4952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_4950_) == 0 {
        let mut v_size_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4951_);
        v_size_4953_ = crate::leanh::lean_ctor_get(v_l_4950_, 0);
        crate::leanh::lean_inc(v_size_4953_);
        v_k_4954_ = crate::leanh::lean_ctor_get(v_l_4950_, 1);
        crate::leanh::lean_inc(v_k_4954_);
        v_v_4955_ = crate::leanh::lean_ctor_get(v_l_4950_, 2);
        crate::leanh::lean_inc(v_v_4955_);
        v_l_4956_ = crate::leanh::lean_ctor_get(v_l_4950_, 3);
        crate::leanh::lean_inc(v_l_4956_);
        v_r_4957_ = crate::leanh::lean_ctor_get(v_l_4950_, 4);
        crate::leanh::lean_inc(v_r_4957_);
        crate::leanh::lean_dec_ref_known(v_l_4950_, 5);
        v___x_4958_ = crate::leanh::lean_apply_5(
            v_h__2_4952_,
            v_size_4953_,
            v_k_4954_,
            v_v_4955_,
            v_l_4956_,
            v_r_4957_,
        );
        return v___x_4958_;
    } else {
        let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4952_);
        v___x_4959_ = crate::leanh::lean_box(0);
        v___x_4960_ = crate::leanh::lean_apply_1(v_h__1_4951_, v___x_4959_);
        return v___x_4960_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(
    mut v_00_u03b1_4961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4962_: *mut crate::leanh::LeanObject,
    mut v_motive_4963_: *mut crate::leanh::LeanObject,
    mut v_l_4964_: *mut crate::leanh::LeanObject,
    mut v_h__1_4965_: *mut crate::leanh::LeanObject,
    mut v_h__2_4966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_4964_) == 0 {
        let mut v_size_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4965_);
        v_size_4967_ = crate::leanh::lean_ctor_get(v_l_4964_, 0);
        crate::leanh::lean_inc(v_size_4967_);
        v_k_4968_ = crate::leanh::lean_ctor_get(v_l_4964_, 1);
        crate::leanh::lean_inc(v_k_4968_);
        v_v_4969_ = crate::leanh::lean_ctor_get(v_l_4964_, 2);
        crate::leanh::lean_inc(v_v_4969_);
        v_l_4970_ = crate::leanh::lean_ctor_get(v_l_4964_, 3);
        crate::leanh::lean_inc(v_l_4970_);
        v_r_4971_ = crate::leanh::lean_ctor_get(v_l_4964_, 4);
        crate::leanh::lean_inc(v_r_4971_);
        crate::leanh::lean_dec_ref_known(v_l_4964_, 5);
        v___x_4972_ = crate::leanh::lean_apply_5(
            v_h__2_4966_,
            v_size_4967_,
            v_k_4968_,
            v_v_4969_,
            v_l_4970_,
            v_r_4971_,
        );
        return v___x_4972_;
    } else {
        let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4966_);
        v___x_4973_ = crate::leanh::lean_box(0);
        v___x_4974_ = crate::leanh::lean_apply_1(v_h__1_4965_, v___x_4973_);
        return v___x_4974_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(
    mut v_r_4975_: *mut crate::leanh::LeanObject,
    mut v_h__1_4976_: *mut crate::leanh::LeanObject,
    mut v_h__2_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_4975_) == 0 {
        let mut v_size_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4976_);
        v_size_4978_ = crate::leanh::lean_ctor_get(v_r_4975_, 0);
        crate::leanh::lean_inc(v_size_4978_);
        v_k_4979_ = crate::leanh::lean_ctor_get(v_r_4975_, 1);
        crate::leanh::lean_inc(v_k_4979_);
        v_v_4980_ = crate::leanh::lean_ctor_get(v_r_4975_, 2);
        crate::leanh::lean_inc(v_v_4980_);
        v_l_4981_ = crate::leanh::lean_ctor_get(v_r_4975_, 3);
        crate::leanh::lean_inc(v_l_4981_);
        v_r_4982_ = crate::leanh::lean_ctor_get(v_r_4975_, 4);
        crate::leanh::lean_inc(v_r_4982_);
        crate::leanh::lean_dec_ref_known(v_r_4975_, 5);
        v___x_4983_ = crate::leanh::lean_apply_7(
            v_h__2_4977_,
            v_size_4978_,
            v_k_4979_,
            v_v_4980_,
            v_l_4981_,
            v_r_4982_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_4983_;
    } else {
        let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4977_);
        v___x_4984_ = crate::leanh::lean_apply_2(
            v_h__1_4976_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_4984_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(
    mut v_00_u03b1_4985_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4986_: *mut crate::leanh::LeanObject,
    mut v_l_4987_: *mut crate::leanh::LeanObject,
    mut v_motive_4988_: *mut crate::leanh::LeanObject,
    mut v_r_4989_: *mut crate::leanh::LeanObject,
    mut v_hr_4990_: *mut crate::leanh::LeanObject,
    mut v_hlr_4991_: *mut crate::leanh::LeanObject,
    mut v_h__1_4992_: *mut crate::leanh::LeanObject,
    mut v_h__2_4993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_4989_) == 0 {
        let mut v_size_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4992_);
        v_size_4994_ = crate::leanh::lean_ctor_get(v_r_4989_, 0);
        crate::leanh::lean_inc(v_size_4994_);
        v_k_4995_ = crate::leanh::lean_ctor_get(v_r_4989_, 1);
        crate::leanh::lean_inc(v_k_4995_);
        v_v_4996_ = crate::leanh::lean_ctor_get(v_r_4989_, 2);
        crate::leanh::lean_inc(v_v_4996_);
        v_l_4997_ = crate::leanh::lean_ctor_get(v_r_4989_, 3);
        crate::leanh::lean_inc(v_l_4997_);
        v_r_4998_ = crate::leanh::lean_ctor_get(v_r_4989_, 4);
        crate::leanh::lean_inc(v_r_4998_);
        crate::leanh::lean_dec_ref_known(v_r_4989_, 5);
        v___x_4999_ = crate::leanh::lean_apply_7(
            v_h__2_4993_,
            v_size_4994_,
            v_k_4995_,
            v_v_4996_,
            v_l_4997_,
            v_r_4998_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_4999_;
    } else {
        let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4993_);
        v___x_5000_ = crate::leanh::lean_apply_2(
            v_h__1_4992_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5000_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(
    mut v_00_u03b1_5001_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5002_: *mut crate::leanh::LeanObject,
    mut v_l_5003_: *mut crate::leanh::LeanObject,
    mut v_motive_5004_: *mut crate::leanh::LeanObject,
    mut v_r_5005_: *mut crate::leanh::LeanObject,
    mut v_hr_5006_: *mut crate::leanh::LeanObject,
    mut v_hlr_5007_: *mut crate::leanh::LeanObject,
    mut v_h__1_5008_: *mut crate::leanh::LeanObject,
    mut v_h__2_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5010_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_5001_, v_00_u03b2_5002_, v_l_5003_, v_motive_5004_, v_r_5005_, v_hr_5006_, v_hlr_5007_, v_h__1_5008_, v_h__2_5009_);
    crate::leanh::lean_dec(v_l_5003_);
    return v_res_5010_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(
    mut v_r_5011_: *mut crate::leanh::LeanObject,
    mut v_h__1_5012_: *mut crate::leanh::LeanObject,
    mut v_h__2_5013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_5011_) == 0 {
        let mut v_size_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5012_);
        v_size_5014_ = crate::leanh::lean_ctor_get(v_r_5011_, 0);
        crate::leanh::lean_inc(v_size_5014_);
        v_k_5015_ = crate::leanh::lean_ctor_get(v_r_5011_, 1);
        crate::leanh::lean_inc(v_k_5015_);
        v_v_5016_ = crate::leanh::lean_ctor_get(v_r_5011_, 2);
        crate::leanh::lean_inc(v_v_5016_);
        v_l_5017_ = crate::leanh::lean_ctor_get(v_r_5011_, 3);
        crate::leanh::lean_inc(v_l_5017_);
        v_r_5018_ = crate::leanh::lean_ctor_get(v_r_5011_, 4);
        crate::leanh::lean_inc(v_r_5018_);
        crate::leanh::lean_dec_ref_known(v_r_5011_, 5);
        v___x_5019_ = crate::leanh::lean_apply_7(
            v_h__2_5013_,
            v_size_5014_,
            v_k_5015_,
            v_v_5016_,
            v_l_5017_,
            v_r_5018_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5019_;
    } else {
        let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5013_);
        v___x_5020_ = crate::leanh::lean_apply_2(
            v_h__1_5012_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5020_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(
    mut v_00_u03b1_5021_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5022_: *mut crate::leanh::LeanObject,
    mut v_sz_5023_: *mut crate::leanh::LeanObject,
    mut v_k_5024_: *mut crate::leanh::LeanObject,
    mut v_v_5025_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5026_: *mut crate::leanh::LeanObject,
    mut v_r_x27_5027_: *mut crate::leanh::LeanObject,
    mut v_motive_5028_: *mut crate::leanh::LeanObject,
    mut v_r_5029_: *mut crate::leanh::LeanObject,
    mut v_hr_5030_: *mut crate::leanh::LeanObject,
    mut v_hlr_5031_: *mut crate::leanh::LeanObject,
    mut v_h__1_5032_: *mut crate::leanh::LeanObject,
    mut v_h__2_5033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_5029_) == 0 {
        let mut v_size_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5032_);
        v_size_5034_ = crate::leanh::lean_ctor_get(v_r_5029_, 0);
        crate::leanh::lean_inc(v_size_5034_);
        v_k_5035_ = crate::leanh::lean_ctor_get(v_r_5029_, 1);
        crate::leanh::lean_inc(v_k_5035_);
        v_v_5036_ = crate::leanh::lean_ctor_get(v_r_5029_, 2);
        crate::leanh::lean_inc(v_v_5036_);
        v_l_5037_ = crate::leanh::lean_ctor_get(v_r_5029_, 3);
        crate::leanh::lean_inc(v_l_5037_);
        v_r_5038_ = crate::leanh::lean_ctor_get(v_r_5029_, 4);
        crate::leanh::lean_inc(v_r_5038_);
        crate::leanh::lean_dec_ref_known(v_r_5029_, 5);
        v___x_5039_ = crate::leanh::lean_apply_7(
            v_h__2_5033_,
            v_size_5034_,
            v_k_5035_,
            v_v_5036_,
            v_l_5037_,
            v_r_5038_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5039_;
    } else {
        let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5033_);
        v___x_5040_ = crate::leanh::lean_apply_2(
            v_h__1_5032_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5040_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(
    mut v_00_u03b1_5041_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5042_: *mut crate::leanh::LeanObject,
    mut v_sz_5043_: *mut crate::leanh::LeanObject,
    mut v_k_5044_: *mut crate::leanh::LeanObject,
    mut v_v_5045_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5046_: *mut crate::leanh::LeanObject,
    mut v_r_x27_5047_: *mut crate::leanh::LeanObject,
    mut v_motive_5048_: *mut crate::leanh::LeanObject,
    mut v_r_5049_: *mut crate::leanh::LeanObject,
    mut v_hr_5050_: *mut crate::leanh::LeanObject,
    mut v_hlr_5051_: *mut crate::leanh::LeanObject,
    mut v_h__1_5052_: *mut crate::leanh::LeanObject,
    mut v_h__2_5053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5054_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_5041_, v_00_u03b2_5042_, v_sz_5043_, v_k_5044_, v_v_5045_, v_l_x27_5046_, v_r_x27_5047_, v_motive_5048_, v_r_5049_, v_hr_5050_, v_hlr_5051_, v_h__1_5052_, v_h__2_5053_);
    crate::leanh::lean_dec(v_r_x27_5047_);
    crate::leanh::lean_dec(v_l_x27_5046_);
    crate::leanh::lean_dec(v_v_5045_);
    crate::leanh::lean_dec(v_k_5044_);
    crate::leanh::lean_dec(v_sz_5043_);
    return v_res_5054_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(
    mut v_t_5055_: *mut crate::leanh::LeanObject,
    mut v_h__1_5056_: *mut crate::leanh::LeanObject,
    mut v_h__2_5057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5055_) == 0 {
        let mut v_size_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5056_);
        v_size_5058_ = crate::leanh::lean_ctor_get(v_t_5055_, 0);
        crate::leanh::lean_inc(v_size_5058_);
        v_k_5059_ = crate::leanh::lean_ctor_get(v_t_5055_, 1);
        crate::leanh::lean_inc(v_k_5059_);
        v_v_5060_ = crate::leanh::lean_ctor_get(v_t_5055_, 2);
        crate::leanh::lean_inc(v_v_5060_);
        v_l_5061_ = crate::leanh::lean_ctor_get(v_t_5055_, 3);
        crate::leanh::lean_inc(v_l_5061_);
        v_r_5062_ = crate::leanh::lean_ctor_get(v_t_5055_, 4);
        crate::leanh::lean_inc(v_r_5062_);
        crate::leanh::lean_dec_ref_known(v_t_5055_, 5);
        v___x_5063_ = crate::leanh::lean_apply_6(
            v_h__2_5057_,
            v_size_5058_,
            v_k_5059_,
            v_v_5060_,
            v_l_5061_,
            v_r_5062_,
            crate::leanh::lean_box(0),
        );
        return v___x_5063_;
    } else {
        let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5057_);
        v___x_5064_ = crate::leanh::lean_apply_1(v_h__1_5056_, crate::leanh::lean_box(0));
        return v___x_5064_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(
    mut v_00_u03b1_5065_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5066_: *mut crate::leanh::LeanObject,
    mut v_motive_5067_: *mut crate::leanh::LeanObject,
    mut v_t_5068_: *mut crate::leanh::LeanObject,
    mut v_hr_5069_: *mut crate::leanh::LeanObject,
    mut v_h__1_5070_: *mut crate::leanh::LeanObject,
    mut v_h__2_5071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5068_) == 0 {
        let mut v_size_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5070_);
        v_size_5072_ = crate::leanh::lean_ctor_get(v_t_5068_, 0);
        crate::leanh::lean_inc(v_size_5072_);
        v_k_5073_ = crate::leanh::lean_ctor_get(v_t_5068_, 1);
        crate::leanh::lean_inc(v_k_5073_);
        v_v_5074_ = crate::leanh::lean_ctor_get(v_t_5068_, 2);
        crate::leanh::lean_inc(v_v_5074_);
        v_l_5075_ = crate::leanh::lean_ctor_get(v_t_5068_, 3);
        crate::leanh::lean_inc(v_l_5075_);
        v_r_5076_ = crate::leanh::lean_ctor_get(v_t_5068_, 4);
        crate::leanh::lean_inc(v_r_5076_);
        crate::leanh::lean_dec_ref_known(v_t_5068_, 5);
        v___x_5077_ = crate::leanh::lean_apply_6(
            v_h__2_5071_,
            v_size_5072_,
            v_k_5073_,
            v_v_5074_,
            v_l_5075_,
            v_r_5076_,
            crate::leanh::lean_box(0),
        );
        return v___x_5077_;
    } else {
        let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5071_);
        v___x_5078_ = crate::leanh::lean_apply_1(v_h__1_5070_, crate::leanh::lean_box(0));
        return v___x_5078_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(
    mut v_x_5079_: u8,
    mut v_h__1_5080_: *mut crate::leanh::LeanObject,
    mut v_h__2_5081_: *mut crate::leanh::LeanObject,
    mut v_h__3_5082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5079_ {
        0 => {
            let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5082_);
            crate::leanh::lean_dec(v_h__2_5081_);
            v___x_5083_ = crate::leanh::lean_box(0);
            v___x_5084_ = crate::leanh::lean_apply_1(v_h__1_5080_, v___x_5083_);
            return v___x_5084_;
        }
        1 => {
            let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5081_);
            crate::leanh::lean_dec(v_h__1_5080_);
            v___x_5085_ = crate::leanh::lean_box(0);
            v___x_5086_ = crate::leanh::lean_apply_1(v_h__3_5082_, v___x_5085_);
            return v___x_5086_;
        }
        _ => {
            let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5082_);
            crate::leanh::lean_dec(v_h__1_5080_);
            v___x_5087_ = crate::leanh::lean_box(0);
            v___x_5088_ = crate::leanh::lean_apply_1(v_h__2_5081_, v___x_5087_);
            return v___x_5088_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(
    mut v_x_5089_: *mut crate::leanh::LeanObject,
    mut v_h__1_5090_: *mut crate::leanh::LeanObject,
    mut v_h__2_5091_: *mut crate::leanh::LeanObject,
    mut v_h__3_5092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_5093_: u8 = 0;
    let mut v_res_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_5093_ = (crate::leanh::lean_unbox(v_x_5089_) as u8);
    v_res_5094_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_36__boxed_5093_, v_h__1_5090_, v_h__2_5091_, v_h__3_5092_);
    return v_res_5094_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(
    mut v_motive_5095_: *mut crate::leanh::LeanObject,
    mut v_x_5096_: u8,
    mut v_h__1_5097_: *mut crate::leanh::LeanObject,
    mut v_h__2_5098_: *mut crate::leanh::LeanObject,
    mut v_h__3_5099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5096_ {
        0 => {
            let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5099_);
            crate::leanh::lean_dec(v_h__2_5098_);
            v___x_5100_ = crate::leanh::lean_box(0);
            v___x_5101_ = crate::leanh::lean_apply_1(v_h__1_5097_, v___x_5100_);
            return v___x_5101_;
        }
        1 => {
            let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5098_);
            crate::leanh::lean_dec(v_h__1_5097_);
            v___x_5102_ = crate::leanh::lean_box(0);
            v___x_5103_ = crate::leanh::lean_apply_1(v_h__3_5099_, v___x_5102_);
            return v___x_5103_;
        }
        _ => {
            let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5099_);
            crate::leanh::lean_dec(v_h__1_5097_);
            v___x_5104_ = crate::leanh::lean_box(0);
            v___x_5105_ = crate::leanh::lean_apply_1(v_h__2_5098_, v___x_5104_);
            return v___x_5105_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(
    mut v_motive_5106_: *mut crate::leanh::LeanObject,
    mut v_x_5107_: *mut crate::leanh::LeanObject,
    mut v_h__1_5108_: *mut crate::leanh::LeanObject,
    mut v_h__2_5109_: *mut crate::leanh::LeanObject,
    mut v_h__3_5110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_5111_: u8 = 0;
    let mut v_res_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_5111_ = (crate::leanh::lean_unbox(v_x_5107_) as u8);
    v_res_5112_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_5106_, v_x_51__boxed_5111_, v_h__1_5108_, v_h__2_5109_, v_h__3_5110_);
    return v_res_5112_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(
    mut v_x_5113_: *mut crate::leanh::LeanObject,
    mut v_h__1_5114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5115_ = crate::leanh::lean_apply_4(
        v_h__1_5114_,
        v_x_5113_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5115_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(
    mut v_00_u03b1_5116_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5117_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5118_: *mut crate::leanh::LeanObject,
    mut v_motive_5119_: *mut crate::leanh::LeanObject,
    mut v_x_5120_: *mut crate::leanh::LeanObject,
    mut v_h__1_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5122_ = crate::leanh::lean_apply_4(
        v_h__1_5121_,
        v_x_5120_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5122_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(
    mut v_00_u03b1_5123_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5124_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5125_: *mut crate::leanh::LeanObject,
    mut v_motive_5126_: *mut crate::leanh::LeanObject,
    mut v_x_5127_: *mut crate::leanh::LeanObject,
    mut v_h__1_5128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5129_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_5123_, v_00_u03b2_5124_, v_l_x27_5125_, v_motive_5126_, v_x_5127_, v_h__1_5128_);
    crate::leanh::lean_dec(v_l_x27_5125_);
    return v_res_5129_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(
    mut v_l_5130_: *mut crate::leanh::LeanObject,
    mut v_h__1_5131_: *mut crate::leanh::LeanObject,
    mut v_h__2_5132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_5130_) == 0 {
        let mut v_size_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5131_);
        v_size_5133_ = crate::leanh::lean_ctor_get(v_l_5130_, 0);
        crate::leanh::lean_inc(v_size_5133_);
        v_k_5134_ = crate::leanh::lean_ctor_get(v_l_5130_, 1);
        crate::leanh::lean_inc(v_k_5134_);
        v_v_5135_ = crate::leanh::lean_ctor_get(v_l_5130_, 2);
        crate::leanh::lean_inc(v_v_5135_);
        v_l_5136_ = crate::leanh::lean_ctor_get(v_l_5130_, 3);
        crate::leanh::lean_inc(v_l_5136_);
        v_r_5137_ = crate::leanh::lean_ctor_get(v_l_5130_, 4);
        crate::leanh::lean_inc(v_r_5137_);
        crate::leanh::lean_dec_ref_known(v_l_5130_, 5);
        v___x_5138_ = crate::leanh::lean_apply_6(
            v_h__2_5132_,
            v_size_5133_,
            v_k_5134_,
            v_v_5135_,
            v_l_5136_,
            v_r_5137_,
            crate::leanh::lean_box(0),
        );
        return v___x_5138_;
    } else {
        let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5132_);
        v___x_5139_ = crate::leanh::lean_apply_1(v_h__1_5131_, crate::leanh::lean_box(0));
        return v___x_5139_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(
    mut v_00_u03b1_5140_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5141_: *mut crate::leanh::LeanObject,
    mut v_motive_5142_: *mut crate::leanh::LeanObject,
    mut v_l_5143_: *mut crate::leanh::LeanObject,
    mut v_hl_5144_: *mut crate::leanh::LeanObject,
    mut v_h__1_5145_: *mut crate::leanh::LeanObject,
    mut v_h__2_5146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_5143_) == 0 {
        let mut v_size_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5145_);
        v_size_5147_ = crate::leanh::lean_ctor_get(v_l_5143_, 0);
        crate::leanh::lean_inc(v_size_5147_);
        v_k_5148_ = crate::leanh::lean_ctor_get(v_l_5143_, 1);
        crate::leanh::lean_inc(v_k_5148_);
        v_v_5149_ = crate::leanh::lean_ctor_get(v_l_5143_, 2);
        crate::leanh::lean_inc(v_v_5149_);
        v_l_5150_ = crate::leanh::lean_ctor_get(v_l_5143_, 3);
        crate::leanh::lean_inc(v_l_5150_);
        v_r_5151_ = crate::leanh::lean_ctor_get(v_l_5143_, 4);
        crate::leanh::lean_inc(v_r_5151_);
        crate::leanh::lean_dec_ref_known(v_l_5143_, 5);
        v___x_5152_ = crate::leanh::lean_apply_6(
            v_h__2_5146_,
            v_size_5147_,
            v_k_5148_,
            v_v_5149_,
            v_l_5150_,
            v_r_5151_,
            crate::leanh::lean_box(0),
        );
        return v___x_5152_;
    } else {
        let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5146_);
        v___x_5153_ = crate::leanh::lean_apply_1(v_h__1_5145_, crate::leanh::lean_box(0));
        return v___x_5153_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(
    mut v_x_5154_: *mut crate::leanh::LeanObject,
    mut v_h__1_5155_: *mut crate::leanh::LeanObject,
    mut v_h__2_5156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5154_) == 0 {
        let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5156_);
        v___x_5157_ = crate::leanh::lean_box(0);
        v___x_5158_ = crate::leanh::lean_apply_1(v_h__1_5155_, v___x_5157_);
        return v___x_5158_;
    } else {
        let mut v_val_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5155_);
        v_val_5159_ = crate::leanh::lean_ctor_get(v_x_5154_, 0);
        crate::leanh::lean_inc(v_val_5159_);
        crate::leanh::lean_dec_ref_known(v_x_5154_, 1);
        v_fst_5160_ = crate::leanh::lean_ctor_get(v_val_5159_, 0);
        crate::leanh::lean_inc(v_fst_5160_);
        v_snd_5161_ = crate::leanh::lean_ctor_get(v_val_5159_, 1);
        crate::leanh::lean_inc(v_snd_5161_);
        crate::leanh::lean_dec(v_val_5159_);
        v___x_5162_ = crate::leanh::lean_apply_2(v_h__2_5156_, v_fst_5160_, v_snd_5161_);
        return v___x_5162_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(
    mut v_00_u03b1_5163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5164_: *mut crate::leanh::LeanObject,
    mut v_motive_5165_: *mut crate::leanh::LeanObject,
    mut v_x_5166_: *mut crate::leanh::LeanObject,
    mut v_h__1_5167_: *mut crate::leanh::LeanObject,
    mut v_h__2_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5166_) == 0 {
        let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5168_);
        v___x_5169_ = crate::leanh::lean_box(0);
        v___x_5170_ = crate::leanh::lean_apply_1(v_h__1_5167_, v___x_5169_);
        return v___x_5170_;
    } else {
        let mut v_val_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5167_);
        v_val_5171_ = crate::leanh::lean_ctor_get(v_x_5166_, 0);
        crate::leanh::lean_inc(v_val_5171_);
        crate::leanh::lean_dec_ref_known(v_x_5166_, 1);
        v_fst_5172_ = crate::leanh::lean_ctor_get(v_val_5171_, 0);
        crate::leanh::lean_inc(v_fst_5172_);
        v_snd_5173_ = crate::leanh::lean_ctor_get(v_val_5171_, 1);
        crate::leanh::lean_inc(v_snd_5173_);
        crate::leanh::lean_dec(v_val_5171_);
        v___x_5174_ = crate::leanh::lean_apply_2(v_h__2_5168_, v_fst_5172_, v_snd_5173_);
        return v___x_5174_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(
    mut v_x_5175_: *mut crate::leanh::LeanObject,
    mut v_h__1_5176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5177_ = crate::leanh::lean_apply_4(
        v_h__1_5176_,
        v_x_5175_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5177_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(
    mut v_00_u03b1_5178_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5179_: *mut crate::leanh::LeanObject,
    mut v_l_5180_: *mut crate::leanh::LeanObject,
    mut v_motive_5181_: *mut crate::leanh::LeanObject,
    mut v_x_5182_: *mut crate::leanh::LeanObject,
    mut v_h__1_5183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5184_ = crate::leanh::lean_apply_4(
        v_h__1_5183_,
        v_x_5182_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5184_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(
    mut v_00_u03b1_5185_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5186_: *mut crate::leanh::LeanObject,
    mut v_l_5187_: *mut crate::leanh::LeanObject,
    mut v_motive_5188_: *mut crate::leanh::LeanObject,
    mut v_x_5189_: *mut crate::leanh::LeanObject,
    mut v_h__1_5190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5191_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_5185_, v_00_u03b2_5186_, v_l_5187_, v_motive_5188_, v_x_5189_, v_h__1_5190_);
    crate::leanh::lean_dec(v_l_5187_);
    return v_res_5191_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(
    mut v_x_5192_: *mut crate::leanh::LeanObject,
    mut v_h__1_5193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5194_ = crate::leanh::lean_apply_4(
        v_h__1_5193_,
        v_x_5192_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5194_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(
    mut v_00_u03b1_5195_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5196_: *mut crate::leanh::LeanObject,
    mut v_l_5197_: *mut crate::leanh::LeanObject,
    mut v_motive_5198_: *mut crate::leanh::LeanObject,
    mut v_x_5199_: *mut crate::leanh::LeanObject,
    mut v_h__1_5200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5201_ = crate::leanh::lean_apply_4(
        v_h__1_5200_,
        v_x_5199_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5201_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(
    mut v_00_u03b1_5202_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5203_: *mut crate::leanh::LeanObject,
    mut v_l_5204_: *mut crate::leanh::LeanObject,
    mut v_motive_5205_: *mut crate::leanh::LeanObject,
    mut v_x_5206_: *mut crate::leanh::LeanObject,
    mut v_h__1_5207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5208_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_5202_, v_00_u03b2_5203_, v_l_5204_, v_motive_5205_, v_x_5206_, v_h__1_5207_);
    crate::leanh::lean_dec(v_l_5204_);
    return v_res_5208_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(
    mut v_x_5209_: *mut crate::leanh::LeanObject,
    mut v_h__1_5210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5211_ = crate::leanh::lean_apply_3(
        v_h__1_5210_,
        v_x_5209_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5211_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(
    mut v_00_u03b1_5212_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5213_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5214_: *mut crate::leanh::LeanObject,
    mut v_motive_5215_: *mut crate::leanh::LeanObject,
    mut v_x_5216_: *mut crate::leanh::LeanObject,
    mut v_h__1_5217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5218_ = crate::leanh::lean_apply_3(
        v_h__1_5217_,
        v_x_5216_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5218_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(
    mut v_00_u03b1_5219_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5220_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5221_: *mut crate::leanh::LeanObject,
    mut v_motive_5222_: *mut crate::leanh::LeanObject,
    mut v_x_5223_: *mut crate::leanh::LeanObject,
    mut v_h__1_5224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5225_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(v_00_u03b1_5219_, v_00_u03b2_5220_, v_l_x27_5221_, v_motive_5222_, v_x_5223_, v_h__1_5224_);
    crate::leanh::lean_dec(v_l_x27_5221_);
    return v_res_5225_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(
    mut v_x_5226_: *mut crate::leanh::LeanObject,
    mut v_h__1_5227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5228_ = crate::leanh::lean_apply_3(
        v_h__1_5227_,
        v_x_5226_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5228_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(
    mut v_00_u03b1_5229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5230_: *mut crate::leanh::LeanObject,
    mut v_r_x27_5231_: *mut crate::leanh::LeanObject,
    mut v_motive_5232_: *mut crate::leanh::LeanObject,
    mut v_x_5233_: *mut crate::leanh::LeanObject,
    mut v_h__1_5234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5235_ = crate::leanh::lean_apply_3(
        v_h__1_5234_,
        v_x_5233_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5235_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(
    mut v_00_u03b1_5236_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5237_: *mut crate::leanh::LeanObject,
    mut v_r_x27_5238_: *mut crate::leanh::LeanObject,
    mut v_motive_5239_: *mut crate::leanh::LeanObject,
    mut v_x_5240_: *mut crate::leanh::LeanObject,
    mut v_h__1_5241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5242_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(v_00_u03b1_5236_, v_00_u03b2_5237_, v_r_x27_5238_, v_motive_5239_, v_x_5240_, v_h__1_5241_);
    crate::leanh::lean_dec(v_r_x27_5238_);
    return v_res_5242_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(
    mut v_r_5243_: *mut crate::leanh::LeanObject,
    mut v_h__1_5244_: *mut crate::leanh::LeanObject,
    mut v_h__2_5245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_5243_) == 0 {
        let mut v_size_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5244_);
        v_size_5246_ = crate::leanh::lean_ctor_get(v_r_5243_, 0);
        crate::leanh::lean_inc(v_size_5246_);
        v_k_5247_ = crate::leanh::lean_ctor_get(v_r_5243_, 1);
        crate::leanh::lean_inc(v_k_5247_);
        v_v_5248_ = crate::leanh::lean_ctor_get(v_r_5243_, 2);
        crate::leanh::lean_inc(v_v_5248_);
        v_l_5249_ = crate::leanh::lean_ctor_get(v_r_5243_, 3);
        crate::leanh::lean_inc(v_l_5249_);
        v_r_5250_ = crate::leanh::lean_ctor_get(v_r_5243_, 4);
        crate::leanh::lean_inc(v_r_5250_);
        crate::leanh::lean_dec_ref_known(v_r_5243_, 5);
        v___x_5251_ = crate::leanh::lean_apply_5(
            v_h__2_5245_,
            v_size_5246_,
            v_k_5247_,
            v_v_5248_,
            v_l_5249_,
            v_r_5250_,
        );
        return v___x_5251_;
    } else {
        let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5245_);
        v___x_5252_ = crate::leanh::lean_box(0);
        v___x_5253_ = crate::leanh::lean_apply_1(v_h__1_5244_, v___x_5252_);
        return v___x_5253_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(
    mut v_00_u03b1_5254_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5255_: *mut crate::leanh::LeanObject,
    mut v_motive_5256_: *mut crate::leanh::LeanObject,
    mut v_r_5257_: *mut crate::leanh::LeanObject,
    mut v_h__1_5258_: *mut crate::leanh::LeanObject,
    mut v_h__2_5259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_5257_) == 0 {
        let mut v_size_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5258_);
        v_size_5260_ = crate::leanh::lean_ctor_get(v_r_5257_, 0);
        crate::leanh::lean_inc(v_size_5260_);
        v_k_5261_ = crate::leanh::lean_ctor_get(v_r_5257_, 1);
        crate::leanh::lean_inc(v_k_5261_);
        v_v_5262_ = crate::leanh::lean_ctor_get(v_r_5257_, 2);
        crate::leanh::lean_inc(v_v_5262_);
        v_l_5263_ = crate::leanh::lean_ctor_get(v_r_5257_, 3);
        crate::leanh::lean_inc(v_l_5263_);
        v_r_5264_ = crate::leanh::lean_ctor_get(v_r_5257_, 4);
        crate::leanh::lean_inc(v_r_5264_);
        crate::leanh::lean_dec_ref_known(v_r_5257_, 5);
        v___x_5265_ = crate::leanh::lean_apply_5(
            v_h__2_5259_,
            v_size_5260_,
            v_k_5261_,
            v_v_5262_,
            v_l_5263_,
            v_r_5264_,
        );
        return v___x_5265_;
    } else {
        let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5259_);
        v___x_5266_ = crate::leanh::lean_box(0);
        v___x_5267_ = crate::leanh::lean_apply_1(v_h__1_5258_, v___x_5266_);
        return v___x_5267_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(
    mut v_x_5268_: *mut crate::leanh::LeanObject,
    mut v_h__1_5269_: *mut crate::leanh::LeanObject,
    mut v_h__2_5270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5268_) == 0 {
        let mut v_size_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5270_);
        v_size_5271_ = crate::leanh::lean_ctor_get(v_x_5268_, 0);
        crate::leanh::lean_inc(v_size_5271_);
        v_k_5272_ = crate::leanh::lean_ctor_get(v_x_5268_, 1);
        crate::leanh::lean_inc(v_k_5272_);
        v_v_5273_ = crate::leanh::lean_ctor_get(v_x_5268_, 2);
        crate::leanh::lean_inc(v_v_5273_);
        v_l_5274_ = crate::leanh::lean_ctor_get(v_x_5268_, 3);
        crate::leanh::lean_inc(v_l_5274_);
        v_r_5275_ = crate::leanh::lean_ctor_get(v_x_5268_, 4);
        crate::leanh::lean_inc(v_r_5275_);
        crate::leanh::lean_dec_ref_known(v_x_5268_, 5);
        v___x_5276_ = crate::leanh::lean_apply_5(
            v_h__1_5269_,
            v_size_5271_,
            v_k_5272_,
            v_v_5273_,
            v_l_5274_,
            v_r_5275_,
        );
        return v___x_5276_;
    } else {
        let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5269_);
        v___x_5277_ = crate::leanh::lean_box(0);
        v___x_5278_ = crate::leanh::lean_apply_1(v_h__2_5270_, v___x_5277_);
        return v___x_5278_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(
    mut v_00_u03b1_5279_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5280_: *mut crate::leanh::LeanObject,
    mut v_motive_5281_: *mut crate::leanh::LeanObject,
    mut v_x_5282_: *mut crate::leanh::LeanObject,
    mut v_h__1_5283_: *mut crate::leanh::LeanObject,
    mut v_h__2_5284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5282_) == 0 {
        let mut v_size_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5284_);
        v_size_5285_ = crate::leanh::lean_ctor_get(v_x_5282_, 0);
        crate::leanh::lean_inc(v_size_5285_);
        v_k_5286_ = crate::leanh::lean_ctor_get(v_x_5282_, 1);
        crate::leanh::lean_inc(v_k_5286_);
        v_v_5287_ = crate::leanh::lean_ctor_get(v_x_5282_, 2);
        crate::leanh::lean_inc(v_v_5287_);
        v_l_5288_ = crate::leanh::lean_ctor_get(v_x_5282_, 3);
        crate::leanh::lean_inc(v_l_5288_);
        v_r_5289_ = crate::leanh::lean_ctor_get(v_x_5282_, 4);
        crate::leanh::lean_inc(v_r_5289_);
        crate::leanh::lean_dec_ref_known(v_x_5282_, 5);
        v___x_5290_ = crate::leanh::lean_apply_5(
            v_h__1_5283_,
            v_size_5285_,
            v_k_5286_,
            v_v_5287_,
            v_l_5288_,
            v_r_5289_,
        );
        return v___x_5290_;
    } else {
        let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5283_);
        v___x_5291_ = crate::leanh::lean_box(0);
        v___x_5292_ = crate::leanh::lean_apply_1(v_h__2_5284_, v___x_5291_);
        return v___x_5292_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(
    mut v_r_5293_: *mut crate::leanh::LeanObject,
    mut v_h__1_5294_: *mut crate::leanh::LeanObject,
    mut v_h__2_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_5293_) == 0 {
        let mut v_size_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5294_);
        v_size_5296_ = crate::leanh::lean_ctor_get(v_r_5293_, 0);
        crate::leanh::lean_inc(v_size_5296_);
        v_k_5297_ = crate::leanh::lean_ctor_get(v_r_5293_, 1);
        crate::leanh::lean_inc(v_k_5297_);
        v_v_5298_ = crate::leanh::lean_ctor_get(v_r_5293_, 2);
        crate::leanh::lean_inc(v_v_5298_);
        v_l_5299_ = crate::leanh::lean_ctor_get(v_r_5293_, 3);
        crate::leanh::lean_inc(v_l_5299_);
        v_r_5300_ = crate::leanh::lean_ctor_get(v_r_5293_, 4);
        crate::leanh::lean_inc(v_r_5300_);
        crate::leanh::lean_dec_ref_known(v_r_5293_, 5);
        v___x_5301_ = crate::leanh::lean_apply_7(
            v_h__2_5295_,
            v_size_5296_,
            v_k_5297_,
            v_v_5298_,
            v_l_5299_,
            v_r_5300_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5301_;
    } else {
        let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5295_);
        v___x_5302_ = crate::leanh::lean_apply_2(
            v_h__1_5294_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5302_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(
    mut v_00_u03b1_5303_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5304_: *mut crate::leanh::LeanObject,
    mut v_motive_5305_: *mut crate::leanh::LeanObject,
    mut v_r_5306_: *mut crate::leanh::LeanObject,
    mut v_hr_5307_: *mut crate::leanh::LeanObject,
    mut v_h__1_5308_: *mut crate::leanh::LeanObject,
    mut v_h__2_5309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_5306_) == 0 {
        let mut v_size_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5308_);
        v_size_5310_ = crate::leanh::lean_ctor_get(v_r_5306_, 0);
        crate::leanh::lean_inc(v_size_5310_);
        v_k_5311_ = crate::leanh::lean_ctor_get(v_r_5306_, 1);
        crate::leanh::lean_inc(v_k_5311_);
        v_v_5312_ = crate::leanh::lean_ctor_get(v_r_5306_, 2);
        crate::leanh::lean_inc(v_v_5312_);
        v_l_5313_ = crate::leanh::lean_ctor_get(v_r_5306_, 3);
        crate::leanh::lean_inc(v_l_5313_);
        v_r_5314_ = crate::leanh::lean_ctor_get(v_r_5306_, 4);
        crate::leanh::lean_inc(v_r_5314_);
        crate::leanh::lean_dec_ref_known(v_r_5306_, 5);
        v___x_5315_ = crate::leanh::lean_apply_7(
            v_h__2_5309_,
            v_size_5310_,
            v_k_5311_,
            v_v_5312_,
            v_l_5313_,
            v_r_5314_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5315_;
    } else {
        let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5309_);
        v___x_5316_ = crate::leanh::lean_apply_2(
            v_h__1_5308_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5316_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(
    mut v_t_5317_: *mut crate::leanh::LeanObject,
    mut v_h__1_5318_: *mut crate::leanh::LeanObject,
    mut v_h__2_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5317_) == 0 {
        let mut v_size_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5318_);
        v_size_5320_ = crate::leanh::lean_ctor_get(v_t_5317_, 0);
        crate::leanh::lean_inc(v_size_5320_);
        v_k_5321_ = crate::leanh::lean_ctor_get(v_t_5317_, 1);
        crate::leanh::lean_inc(v_k_5321_);
        v_v_5322_ = crate::leanh::lean_ctor_get(v_t_5317_, 2);
        crate::leanh::lean_inc(v_v_5322_);
        v_l_5323_ = crate::leanh::lean_ctor_get(v_t_5317_, 3);
        crate::leanh::lean_inc(v_l_5323_);
        v_r_5324_ = crate::leanh::lean_ctor_get(v_t_5317_, 4);
        crate::leanh::lean_inc(v_r_5324_);
        crate::leanh::lean_dec_ref_known(v_t_5317_, 5);
        v___x_5325_ = crate::leanh::lean_apply_5(
            v_h__2_5319_,
            v_size_5320_,
            v_k_5321_,
            v_v_5322_,
            v_l_5323_,
            v_r_5324_,
        );
        return v___x_5325_;
    } else {
        let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5319_);
        v___x_5326_ = crate::leanh::lean_box(0);
        v___x_5327_ = crate::leanh::lean_apply_1(v_h__1_5318_, v___x_5326_);
        return v___x_5327_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(
    mut v_00_u03b1_5328_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5329_: *mut crate::leanh::LeanObject,
    mut v_motive_5330_: *mut crate::leanh::LeanObject,
    mut v_t_5331_: *mut crate::leanh::LeanObject,
    mut v_h__1_5332_: *mut crate::leanh::LeanObject,
    mut v_h__2_5333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5331_) == 0 {
        let mut v_size_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5332_);
        v_size_5334_ = crate::leanh::lean_ctor_get(v_t_5331_, 0);
        crate::leanh::lean_inc(v_size_5334_);
        v_k_5335_ = crate::leanh::lean_ctor_get(v_t_5331_, 1);
        crate::leanh::lean_inc(v_k_5335_);
        v_v_5336_ = crate::leanh::lean_ctor_get(v_t_5331_, 2);
        crate::leanh::lean_inc(v_v_5336_);
        v_l_5337_ = crate::leanh::lean_ctor_get(v_t_5331_, 3);
        crate::leanh::lean_inc(v_l_5337_);
        v_r_5338_ = crate::leanh::lean_ctor_get(v_t_5331_, 4);
        crate::leanh::lean_inc(v_r_5338_);
        crate::leanh::lean_dec_ref_known(v_t_5331_, 5);
        v___x_5339_ = crate::leanh::lean_apply_5(
            v_h__2_5333_,
            v_size_5334_,
            v_k_5335_,
            v_v_5336_,
            v_l_5337_,
            v_r_5338_,
        );
        return v___x_5339_;
    } else {
        let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5333_);
        v___x_5340_ = crate::leanh::lean_box(0);
        v___x_5341_ = crate::leanh::lean_apply_1(v_h__1_5332_, v___x_5340_);
        return v___x_5341_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(
    mut v_x_5342_: *mut crate::leanh::LeanObject,
    mut v_h__1_5343_: *mut crate::leanh::LeanObject,
    mut v_h__2_5344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5342_) == 0 {
        let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5344_);
        v___x_5345_ = crate::leanh::lean_box(0);
        v___x_5346_ = crate::leanh::lean_apply_1(v_h__1_5343_, v___x_5345_);
        return v___x_5346_;
    } else {
        let mut v_val_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5343_);
        v_val_5347_ = crate::leanh::lean_ctor_get(v_x_5342_, 0);
        crate::leanh::lean_inc(v_val_5347_);
        crate::leanh::lean_dec_ref_known(v_x_5342_, 1);
        v___x_5348_ = crate::leanh::lean_apply_1(v_h__2_5344_, v_val_5347_);
        return v___x_5348_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(
    mut v_00_u03b1_5349_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5350_: *mut crate::leanh::LeanObject,
    mut v_motive_5351_: *mut crate::leanh::LeanObject,
    mut v_x_5352_: *mut crate::leanh::LeanObject,
    mut v_h__1_5353_: *mut crate::leanh::LeanObject,
    mut v_h__2_5354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5352_) == 0 {
        let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5354_);
        v___x_5355_ = crate::leanh::lean_box(0);
        v___x_5356_ = crate::leanh::lean_apply_1(v_h__1_5353_, v___x_5355_);
        return v___x_5356_;
    } else {
        let mut v_val_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5353_);
        v_val_5357_ = crate::leanh::lean_ctor_get(v_x_5352_, 0);
        crate::leanh::lean_inc(v_val_5357_);
        crate::leanh::lean_dec_ref_known(v_x_5352_, 1);
        v___x_5358_ = crate::leanh::lean_apply_1(v_h__2_5354_, v_val_5357_);
        return v___x_5358_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(
    mut v_t_5359_: *mut crate::leanh::LeanObject,
    mut v_h__1_5360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_5361_ = crate::leanh::lean_ctor_get(v_t_5359_, 0);
    crate::leanh::lean_inc(v_size_5361_);
    v_k_5362_ = crate::leanh::lean_ctor_get(v_t_5359_, 1);
    crate::leanh::lean_inc(v_k_5362_);
    v_v_5363_ = crate::leanh::lean_ctor_get(v_t_5359_, 2);
    crate::leanh::lean_inc(v_v_5363_);
    v_l_5364_ = crate::leanh::lean_ctor_get(v_t_5359_, 3);
    crate::leanh::lean_inc(v_l_5364_);
    v_r_5365_ = crate::leanh::lean_ctor_get(v_t_5359_, 4);
    crate::leanh::lean_inc(v_r_5365_);
    crate::leanh::lean_dec(v_t_5359_);
    v___x_5366_ = crate::leanh::lean_apply_6(
        v_h__1_5360_,
        v_size_5361_,
        v_k_5362_,
        v_v_5363_,
        v_l_5364_,
        v_r_5365_,
        crate::leanh::lean_box(0),
    );
    return v___x_5366_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(
    mut v_00_u03b1_5367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5368_: *mut crate::leanh::LeanObject,
    mut v_inst_5369_: *mut crate::leanh::LeanObject,
    mut v_k_5370_: *mut crate::leanh::LeanObject,
    mut v_motive_5371_: *mut crate::leanh::LeanObject,
    mut v_t_5372_: *mut crate::leanh::LeanObject,
    mut v_hlk_5373_: *mut crate::leanh::LeanObject,
    mut v_h__1_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_5375_ = crate::leanh::lean_ctor_get(v_t_5372_, 0);
    crate::leanh::lean_inc(v_size_5375_);
    v_k_5376_ = crate::leanh::lean_ctor_get(v_t_5372_, 1);
    crate::leanh::lean_inc(v_k_5376_);
    v_v_5377_ = crate::leanh::lean_ctor_get(v_t_5372_, 2);
    crate::leanh::lean_inc(v_v_5377_);
    v_l_5378_ = crate::leanh::lean_ctor_get(v_t_5372_, 3);
    crate::leanh::lean_inc(v_l_5378_);
    v_r_5379_ = crate::leanh::lean_ctor_get(v_t_5372_, 4);
    crate::leanh::lean_inc(v_r_5379_);
    crate::leanh::lean_dec(v_t_5372_);
    v___x_5380_ = crate::leanh::lean_apply_6(
        v_h__1_5374_,
        v_size_5375_,
        v_k_5376_,
        v_v_5377_,
        v_l_5378_,
        v_r_5379_,
        crate::leanh::lean_box(0),
    );
    return v___x_5380_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(
    mut v_00_u03b1_5381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5382_: *mut crate::leanh::LeanObject,
    mut v_inst_5383_: *mut crate::leanh::LeanObject,
    mut v_k_5384_: *mut crate::leanh::LeanObject,
    mut v_motive_5385_: *mut crate::leanh::LeanObject,
    mut v_t_5386_: *mut crate::leanh::LeanObject,
    mut v_hlk_5387_: *mut crate::leanh::LeanObject,
    mut v_h__1_5388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5389_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(v_00_u03b1_5381_, v_00_u03b4_5382_, v_inst_5383_, v_k_5384_, v_motive_5385_, v_t_5386_, v_hlk_5387_, v_h__1_5388_);
    crate::leanh::lean_dec(v_k_5384_);
    crate::leanh::lean_dec_ref(v_inst_5383_);
    return v_res_5389_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(
    mut v_x_5390_: *mut crate::leanh::LeanObject,
    mut v_x_5391_: *mut crate::leanh::LeanObject,
    mut v_h__1_5392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_5393_ = crate::leanh::lean_ctor_get(v_x_5390_, 0);
    crate::leanh::lean_inc(v_size_5393_);
    v_k_5394_ = crate::leanh::lean_ctor_get(v_x_5390_, 1);
    crate::leanh::lean_inc(v_k_5394_);
    v_v_5395_ = crate::leanh::lean_ctor_get(v_x_5390_, 2);
    crate::leanh::lean_inc(v_v_5395_);
    v_l_5396_ = crate::leanh::lean_ctor_get(v_x_5390_, 3);
    crate::leanh::lean_inc(v_l_5396_);
    v_r_5397_ = crate::leanh::lean_ctor_get(v_x_5390_, 4);
    crate::leanh::lean_inc(v_r_5397_);
    crate::leanh::lean_dec(v_x_5390_);
    v___x_5398_ = crate::leanh::lean_apply_8(
        v_h__1_5392_,
        v_size_5393_,
        v_k_5394_,
        v_v_5395_,
        v_l_5396_,
        v_r_5397_,
        crate::leanh::lean_box(0),
        v_x_5391_,
        crate::leanh::lean_box(0),
    );
    return v___x_5398_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(
    mut v_00_u03b1_5399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5400_: *mut crate::leanh::LeanObject,
    mut v_motive_5401_: *mut crate::leanh::LeanObject,
    mut v_x_5402_: *mut crate::leanh::LeanObject,
    mut v_x_5403_: *mut crate::leanh::LeanObject,
    mut v_x_5404_: *mut crate::leanh::LeanObject,
    mut v_x_5405_: *mut crate::leanh::LeanObject,
    mut v_h__1_5406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_5407_ = crate::leanh::lean_ctor_get(v_x_5402_, 0);
    crate::leanh::lean_inc(v_size_5407_);
    v_k_5408_ = crate::leanh::lean_ctor_get(v_x_5402_, 1);
    crate::leanh::lean_inc(v_k_5408_);
    v_v_5409_ = crate::leanh::lean_ctor_get(v_x_5402_, 2);
    crate::leanh::lean_inc(v_v_5409_);
    v_l_5410_ = crate::leanh::lean_ctor_get(v_x_5402_, 3);
    crate::leanh::lean_inc(v_l_5410_);
    v_r_5411_ = crate::leanh::lean_ctor_get(v_x_5402_, 4);
    crate::leanh::lean_inc(v_r_5411_);
    crate::leanh::lean_dec(v_x_5402_);
    v___x_5412_ = crate::leanh::lean_apply_8(
        v_h__1_5406_,
        v_size_5407_,
        v_k_5408_,
        v_v_5409_,
        v_l_5410_,
        v_r_5411_,
        crate::leanh::lean_box(0),
        v_x_5404_,
        crate::leanh::lean_box(0),
    );
    return v___x_5412_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(
    mut v_x_5413_: u8,
    mut v_h__1_5414_: *mut crate::leanh::LeanObject,
    mut v_h__2_5415_: *mut crate::leanh::LeanObject,
    mut v_h__3_5416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5413_ {
        0 => {
            let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5416_);
            crate::leanh::lean_dec(v_h__2_5415_);
            v___x_5417_ = crate::leanh::lean_apply_1(v_h__1_5414_, crate::leanh::lean_box(0));
            return v___x_5417_;
        }
        1 => {
            let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5416_);
            crate::leanh::lean_dec(v_h__1_5414_);
            v___x_5418_ = crate::leanh::lean_apply_1(v_h__2_5415_, crate::leanh::lean_box(0));
            return v___x_5418_;
        }
        _ => {
            let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5415_);
            crate::leanh::lean_dec(v_h__1_5414_);
            v___x_5419_ = crate::leanh::lean_apply_1(v_h__3_5416_, crate::leanh::lean_box(0));
            return v___x_5419_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(
    mut v_x_5420_: *mut crate::leanh::LeanObject,
    mut v_h__1_5421_: *mut crate::leanh::LeanObject,
    mut v_h__2_5422_: *mut crate::leanh::LeanObject,
    mut v_h__3_5423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_5424_: u8 = 0;
    let mut v_res_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_5424_ = (crate::leanh::lean_unbox(v_x_5420_) as u8);
    v_res_5425_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_33__boxed_5424_, v_h__1_5421_, v_h__2_5422_, v_h__3_5423_);
    return v_res_5425_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(
    mut v_motive_5426_: *mut crate::leanh::LeanObject,
    mut v_x_5427_: u8,
    mut v_h__1_5428_: *mut crate::leanh::LeanObject,
    mut v_h__2_5429_: *mut crate::leanh::LeanObject,
    mut v_h__3_5430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5427_ {
        0 => {
            let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5430_);
            crate::leanh::lean_dec(v_h__2_5429_);
            v___x_5431_ = crate::leanh::lean_apply_1(v_h__1_5428_, crate::leanh::lean_box(0));
            return v___x_5431_;
        }
        1 => {
            let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5430_);
            crate::leanh::lean_dec(v_h__1_5428_);
            v___x_5432_ = crate::leanh::lean_apply_1(v_h__2_5429_, crate::leanh::lean_box(0));
            return v___x_5432_;
        }
        _ => {
            let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5429_);
            crate::leanh::lean_dec(v_h__1_5428_);
            v___x_5433_ = crate::leanh::lean_apply_1(v_h__3_5430_, crate::leanh::lean_box(0));
            return v___x_5433_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(
    mut v_motive_5434_: *mut crate::leanh::LeanObject,
    mut v_x_5435_: *mut crate::leanh::LeanObject,
    mut v_h__1_5436_: *mut crate::leanh::LeanObject,
    mut v_h__2_5437_: *mut crate::leanh::LeanObject,
    mut v_h__3_5438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42__boxed_5439_: u8 = 0;
    let mut v_res_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_5439_ = (crate::leanh::lean_unbox(v_x_5435_) as u8);
    v_res_5440_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_5434_, v_x_42__boxed_5439_, v_h__1_5436_, v_h__2_5437_, v_h__3_5438_);
    return v_res_5440_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(
    mut v_x_5441_: *mut crate::leanh::LeanObject,
    mut v_x_5442_: *mut crate::leanh::LeanObject,
    mut v_h__1_5443_: *mut crate::leanh::LeanObject,
    mut v_h__2_5444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5441_) == 0 {
        let mut v_size_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5443_);
        v_size_5445_ = crate::leanh::lean_ctor_get(v_x_5441_, 0);
        crate::leanh::lean_inc(v_size_5445_);
        v_k_5446_ = crate::leanh::lean_ctor_get(v_x_5441_, 1);
        crate::leanh::lean_inc(v_k_5446_);
        v_v_5447_ = crate::leanh::lean_ctor_get(v_x_5441_, 2);
        crate::leanh::lean_inc(v_v_5447_);
        v_l_5448_ = crate::leanh::lean_ctor_get(v_x_5441_, 3);
        crate::leanh::lean_inc(v_l_5448_);
        v_r_5449_ = crate::leanh::lean_ctor_get(v_x_5441_, 4);
        crate::leanh::lean_inc(v_r_5449_);
        crate::leanh::lean_dec_ref_known(v_x_5441_, 5);
        v___x_5450_ = crate::leanh::lean_apply_6(
            v_h__2_5444_,
            v_size_5445_,
            v_k_5446_,
            v_v_5447_,
            v_l_5448_,
            v_r_5449_,
            v_x_5442_,
        );
        return v___x_5450_;
    } else {
        let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5444_);
        v___x_5451_ = crate::leanh::lean_apply_1(v_h__1_5443_, v_x_5442_);
        return v___x_5451_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(
    mut v_00_u03b1_5452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5453_: *mut crate::leanh::LeanObject,
    mut v_motive_5454_: *mut crate::leanh::LeanObject,
    mut v_x_5455_: *mut crate::leanh::LeanObject,
    mut v_x_5456_: *mut crate::leanh::LeanObject,
    mut v_h__1_5457_: *mut crate::leanh::LeanObject,
    mut v_h__2_5458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5455_) == 0 {
        let mut v_size_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5457_);
        v_size_5459_ = crate::leanh::lean_ctor_get(v_x_5455_, 0);
        crate::leanh::lean_inc(v_size_5459_);
        v_k_5460_ = crate::leanh::lean_ctor_get(v_x_5455_, 1);
        crate::leanh::lean_inc(v_k_5460_);
        v_v_5461_ = crate::leanh::lean_ctor_get(v_x_5455_, 2);
        crate::leanh::lean_inc(v_v_5461_);
        v_l_5462_ = crate::leanh::lean_ctor_get(v_x_5455_, 3);
        crate::leanh::lean_inc(v_l_5462_);
        v_r_5463_ = crate::leanh::lean_ctor_get(v_x_5455_, 4);
        crate::leanh::lean_inc(v_r_5463_);
        crate::leanh::lean_dec_ref_known(v_x_5455_, 5);
        v___x_5464_ = crate::leanh::lean_apply_6(
            v_h__2_5458_,
            v_size_5459_,
            v_k_5460_,
            v_v_5461_,
            v_l_5462_,
            v_r_5463_,
            v_x_5456_,
        );
        return v___x_5464_;
    } else {
        let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5458_);
        v___x_5465_ = crate::leanh::lean_apply_1(v_h__1_5457_, v_x_5456_);
        return v___x_5465_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(
    mut v_x_5466_: u8,
    mut v_h__1_5467_: *mut crate::leanh::LeanObject,
    mut v_h__2_5468_: *mut crate::leanh::LeanObject,
    mut v_h__3_5469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5466_ {
        0 => {
            let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5469_);
            crate::leanh::lean_dec(v_h__2_5468_);
            v___x_5470_ = crate::leanh::lean_box(0);
            v___x_5471_ = crate::leanh::lean_apply_1(v_h__1_5467_, v___x_5470_);
            return v___x_5471_;
        }
        1 => {
            let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5469_);
            crate::leanh::lean_dec(v_h__1_5467_);
            v___x_5472_ = crate::leanh::lean_box(0);
            v___x_5473_ = crate::leanh::lean_apply_1(v_h__2_5468_, v___x_5472_);
            return v___x_5473_;
        }
        _ => {
            let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5468_);
            crate::leanh::lean_dec(v_h__1_5467_);
            v___x_5474_ = crate::leanh::lean_box(0);
            v___x_5475_ = crate::leanh::lean_apply_1(v_h__3_5469_, v___x_5474_);
            return v___x_5475_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(
    mut v_x_5476_: *mut crate::leanh::LeanObject,
    mut v_h__1_5477_: *mut crate::leanh::LeanObject,
    mut v_h__2_5478_: *mut crate::leanh::LeanObject,
    mut v_h__3_5479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_5480_: u8 = 0;
    let mut v_res_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_5480_ = (crate::leanh::lean_unbox(v_x_5476_) as u8);
    v_res_5481_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_36__boxed_5480_, v_h__1_5477_, v_h__2_5478_, v_h__3_5479_);
    return v_res_5481_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(
    mut v_motive_5482_: *mut crate::leanh::LeanObject,
    mut v_x_5483_: u8,
    mut v_h__1_5484_: *mut crate::leanh::LeanObject,
    mut v_h__2_5485_: *mut crate::leanh::LeanObject,
    mut v_h__3_5486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5483_ {
        0 => {
            let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5486_);
            crate::leanh::lean_dec(v_h__2_5485_);
            v___x_5487_ = crate::leanh::lean_box(0);
            v___x_5488_ = crate::leanh::lean_apply_1(v_h__1_5484_, v___x_5487_);
            return v___x_5488_;
        }
        1 => {
            let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5486_);
            crate::leanh::lean_dec(v_h__1_5484_);
            v___x_5489_ = crate::leanh::lean_box(0);
            v___x_5490_ = crate::leanh::lean_apply_1(v_h__2_5485_, v___x_5489_);
            return v___x_5490_;
        }
        _ => {
            let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5485_);
            crate::leanh::lean_dec(v_h__1_5484_);
            v___x_5491_ = crate::leanh::lean_box(0);
            v___x_5492_ = crate::leanh::lean_apply_1(v_h__3_5486_, v___x_5491_);
            return v___x_5492_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(
    mut v_motive_5493_: *mut crate::leanh::LeanObject,
    mut v_x_5494_: *mut crate::leanh::LeanObject,
    mut v_h__1_5495_: *mut crate::leanh::LeanObject,
    mut v_h__2_5496_: *mut crate::leanh::LeanObject,
    mut v_h__3_5497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_5498_: u8 = 0;
    let mut v_res_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_5498_ = (crate::leanh::lean_unbox(v_x_5494_) as u8);
    v_res_5499_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_5493_, v_x_51__boxed_5498_, v_h__1_5495_, v_h__2_5496_, v_h__3_5497_);
    return v_res_5499_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(
    mut v_x_5500_: *mut crate::leanh::LeanObject,
    mut v_x_5501_: *mut crate::leanh::LeanObject,
    mut v_x_5502_: *mut crate::leanh::LeanObject,
    mut v_h__1_5503_: *mut crate::leanh::LeanObject,
    mut v_h__2_5504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5500_) == 0 {
        let mut v_size_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5503_);
        v_size_5505_ = crate::leanh::lean_ctor_get(v_x_5500_, 0);
        crate::leanh::lean_inc(v_size_5505_);
        v_k_5506_ = crate::leanh::lean_ctor_get(v_x_5500_, 1);
        crate::leanh::lean_inc(v_k_5506_);
        v_v_5507_ = crate::leanh::lean_ctor_get(v_x_5500_, 2);
        crate::leanh::lean_inc(v_v_5507_);
        v_l_5508_ = crate::leanh::lean_ctor_get(v_x_5500_, 3);
        crate::leanh::lean_inc(v_l_5508_);
        v_r_5509_ = crate::leanh::lean_ctor_get(v_x_5500_, 4);
        crate::leanh::lean_inc(v_r_5509_);
        crate::leanh::lean_dec_ref_known(v_x_5500_, 5);
        v___x_5510_ = crate::leanh::lean_apply_7(
            v_h__2_5504_,
            v_size_5505_,
            v_k_5506_,
            v_v_5507_,
            v_l_5508_,
            v_r_5509_,
            v_x_5501_,
            v_x_5502_,
        );
        return v___x_5510_;
    } else {
        let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5504_);
        v___x_5511_ = crate::leanh::lean_apply_2(v_h__1_5503_, v_x_5501_, v_x_5502_);
        return v___x_5511_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(
    mut v_00_u03b1_5512_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5513_: *mut crate::leanh::LeanObject,
    mut v_motive_5514_: *mut crate::leanh::LeanObject,
    mut v_x_5515_: *mut crate::leanh::LeanObject,
    mut v_x_5516_: *mut crate::leanh::LeanObject,
    mut v_x_5517_: *mut crate::leanh::LeanObject,
    mut v_h__1_5518_: *mut crate::leanh::LeanObject,
    mut v_h__2_5519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5515_) == 0 {
        let mut v_size_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5518_);
        v_size_5520_ = crate::leanh::lean_ctor_get(v_x_5515_, 0);
        crate::leanh::lean_inc(v_size_5520_);
        v_k_5521_ = crate::leanh::lean_ctor_get(v_x_5515_, 1);
        crate::leanh::lean_inc(v_k_5521_);
        v_v_5522_ = crate::leanh::lean_ctor_get(v_x_5515_, 2);
        crate::leanh::lean_inc(v_v_5522_);
        v_l_5523_ = crate::leanh::lean_ctor_get(v_x_5515_, 3);
        crate::leanh::lean_inc(v_l_5523_);
        v_r_5524_ = crate::leanh::lean_ctor_get(v_x_5515_, 4);
        crate::leanh::lean_inc(v_r_5524_);
        crate::leanh::lean_dec_ref_known(v_x_5515_, 5);
        v___x_5525_ = crate::leanh::lean_apply_7(
            v_h__2_5519_,
            v_size_5520_,
            v_k_5521_,
            v_v_5522_,
            v_l_5523_,
            v_r_5524_,
            v_x_5516_,
            v_x_5517_,
        );
        return v___x_5525_;
    } else {
        let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5519_);
        v___x_5526_ = crate::leanh::lean_apply_2(v_h__1_5518_, v_x_5516_, v_x_5517_);
        return v___x_5526_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(
    mut v_x_5527_: *mut crate::leanh::LeanObject,
    mut v_x_5528_: *mut crate::leanh::LeanObject,
    mut v_x_5529_: *mut crate::leanh::LeanObject,
    mut v_h__1_5530_: *mut crate::leanh::LeanObject,
    mut v_h__2_5531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5527_) == 0 {
        let mut v_size_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5530_);
        v_size_5532_ = crate::leanh::lean_ctor_get(v_x_5527_, 0);
        crate::leanh::lean_inc(v_size_5532_);
        v_k_5533_ = crate::leanh::lean_ctor_get(v_x_5527_, 1);
        crate::leanh::lean_inc(v_k_5533_);
        v_v_5534_ = crate::leanh::lean_ctor_get(v_x_5527_, 2);
        crate::leanh::lean_inc(v_v_5534_);
        v_l_5535_ = crate::leanh::lean_ctor_get(v_x_5527_, 3);
        crate::leanh::lean_inc(v_l_5535_);
        v_r_5536_ = crate::leanh::lean_ctor_get(v_x_5527_, 4);
        crate::leanh::lean_inc(v_r_5536_);
        crate::leanh::lean_dec_ref_known(v_x_5527_, 5);
        v___x_5537_ = crate::leanh::lean_apply_7(
            v_h__2_5531_,
            v_size_5532_,
            v_k_5533_,
            v_v_5534_,
            v_l_5535_,
            v_r_5536_,
            v_x_5528_,
            v_x_5529_,
        );
        return v___x_5537_;
    } else {
        let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5531_);
        v___x_5538_ = crate::leanh::lean_apply_2(v_h__1_5530_, v_x_5528_, v_x_5529_);
        return v___x_5538_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(
    mut v_00_u03b1_5539_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5540_: *mut crate::leanh::LeanObject,
    mut v_motive_5541_: *mut crate::leanh::LeanObject,
    mut v_x_5542_: *mut crate::leanh::LeanObject,
    mut v_x_5543_: *mut crate::leanh::LeanObject,
    mut v_x_5544_: *mut crate::leanh::LeanObject,
    mut v_h__1_5545_: *mut crate::leanh::LeanObject,
    mut v_h__2_5546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5542_) == 0 {
        let mut v_size_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5545_);
        v_size_5547_ = crate::leanh::lean_ctor_get(v_x_5542_, 0);
        crate::leanh::lean_inc(v_size_5547_);
        v_k_5548_ = crate::leanh::lean_ctor_get(v_x_5542_, 1);
        crate::leanh::lean_inc(v_k_5548_);
        v_v_5549_ = crate::leanh::lean_ctor_get(v_x_5542_, 2);
        crate::leanh::lean_inc(v_v_5549_);
        v_l_5550_ = crate::leanh::lean_ctor_get(v_x_5542_, 3);
        crate::leanh::lean_inc(v_l_5550_);
        v_r_5551_ = crate::leanh::lean_ctor_get(v_x_5542_, 4);
        crate::leanh::lean_inc(v_r_5551_);
        crate::leanh::lean_dec_ref_known(v_x_5542_, 5);
        v___x_5552_ = crate::leanh::lean_apply_7(
            v_h__2_5546_,
            v_size_5547_,
            v_k_5548_,
            v_v_5549_,
            v_l_5550_,
            v_r_5551_,
            v_x_5543_,
            v_x_5544_,
        );
        return v___x_5552_;
    } else {
        let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5546_);
        v___x_5553_ = crate::leanh::lean_apply_2(v_h__1_5545_, v_x_5543_, v_x_5544_);
        return v___x_5553_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(
    mut v_x_5554_: *mut crate::leanh::LeanObject,
    mut v_c_5555_: *mut crate::leanh::LeanObject,
    mut v_x_5556_: *mut crate::leanh::LeanObject,
    mut v_r_5557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5562_: u8 = 0;
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_c_5555_) == 0 {
                    v___x_5558_ = l_List_head_x3f___redArg(v_r_5557_);
                    return v___x_5558_;
                } else {
                    v_val_5559_ = crate::leanh::lean_ctor_get(v_c_5555_, 0);
                    v_isSharedCheck_5566_ = (!crate::leanh::lean_is_exclusive(v_c_5555_)) as u8;
                    if v_isSharedCheck_5566_ == 0 {
                        v___x_5561_ = v_c_5555_;
                        v_isShared_5562_ = v_isSharedCheck_5566_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5559_);
                        crate::leanh::lean_dec(v_c_5555_);
                        v___x_5561_ = crate::leanh::lean_box(0);
                        v_isShared_5562_ = v_isSharedCheck_5566_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5562_ == 0 {
                    v___x_5564_ = v___x_5561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_val_5559_);
                    v___x_5564_ = v_reuseFailAlloc_5565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed(
    mut v_x_5567_: *mut crate::leanh::LeanObject,
    mut v_c_5568_: *mut crate::leanh::LeanObject,
    mut v_x_5569_: *mut crate::leanh::LeanObject,
    mut v_r_5570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5571_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(
        v_x_5567_, v_c_5568_, v_x_5569_, v_r_5570_,
    );
    crate::leanh::lean_dec(v_r_5570_);
    crate::leanh::lean_dec(v_x_5567_);
    return v_res_5571_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(
    mut v_inst_5573_: *mut crate::leanh::LeanObject,
    mut v_k_5574_: *mut crate::leanh::LeanObject,
    mut v_t_5575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5576_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0;
    v___x_5577_ = crate::leanh::lean_apply_1(v_inst_5573_, v_k_5574_);
    v___x_5578_ =
        l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_5577_, v_t_5575_, v___f_5576_);
    return v___x_5578_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(
    mut v_00_u03b1_5579_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5580_: *mut crate::leanh::LeanObject,
    mut v_inst_5581_: *mut crate::leanh::LeanObject,
    mut v_k_5582_: *mut crate::leanh::LeanObject,
    mut v_t_5583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5584_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(
        v_inst_5581_,
        v_k_5582_,
        v_t_5583_,
    );
    return v___x_5584_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(
    mut v_x_5585_: *mut crate::leanh::LeanObject,
    mut v_x_5586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5597_: u8 = 0;
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_5586_) {
                0 => {
                    v_a_5587_ = crate::leanh::lean_ctor_get(v_x_5586_, 0);
                    crate::leanh::lean_inc(v_a_5587_);
                    v_a_5588_ = crate::leanh::lean_ctor_get(v_x_5586_, 1);
                    crate::leanh::lean_inc(v_a_5588_);
                    crate::leanh::lean_dec_ref_known(v_x_5586_, 3);
                    v___x_5589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5589_, 0, v_a_5587_);
                    crate::leanh::lean_ctor_set(v___x_5589_, 1, v_a_5588_);
                    v___x_5590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5590_, 0, v___x_5589_);
                    return v___x_5590_;
                }
                1 => {
                    v_a_5591_ = crate::leanh::lean_ctor_get(v_x_5586_, 1);
                    crate::leanh::lean_inc(v_a_5591_);
                    if crate::leanh::lean_obj_tag(v_a_5591_) == 0 {
                        v_a_5592_ = crate::leanh::lean_ctor_get(v_x_5586_, 2);
                        crate::leanh::lean_inc(v_a_5592_);
                        crate::leanh::lean_dec_ref_known(v_x_5586_, 3);
                        v___x_5593_ = l_List_head_x3f___redArg(v_a_5592_);
                        crate::leanh::lean_dec(v_a_5592_);
                        if crate::leanh::lean_obj_tag(v___x_5593_) == 0 {
                            crate::leanh::lean_inc(v_x_5585_);
                            return v_x_5585_;
                        } else {
                            return v___x_5593_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_5586_, 3);
                        v_val_5594_ = crate::leanh::lean_ctor_get(v_a_5591_, 0);
                        v_isSharedCheck_5601_ = (!crate::leanh::lean_is_exclusive(v_a_5591_)) as u8;
                        if v_isSharedCheck_5601_ == 0 {
                            v___x_5596_ = v_a_5591_;
                            v_isShared_5597_ = v_isSharedCheck_5601_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5594_);
                            crate::leanh::lean_dec(v_a_5591_);
                            v___x_5596_ = crate::leanh::lean_box(0);
                            v_isShared_5597_ = v_isSharedCheck_5601_;
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref_known(v_x_5586_, 3);
                    crate::leanh::lean_inc(v_x_5585_);
                    return v_x_5585_;
                }
            },
            1 => {
                if v_isShared_5597_ == 0 {
                    v___x_5599_ = v___x_5596_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_val_5594_);
                    v___x_5599_ = v_reuseFailAlloc_5600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed(
    mut v_x_5602_: *mut crate::leanh::LeanObject,
    mut v_x_5603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5604_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(
        v_x_5602_, v_x_5603_,
    );
    crate::leanh::lean_dec(v_x_5602_);
    return v_res_5604_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(
    mut v_inst_5606_: *mut crate::leanh::LeanObject,
    mut v_k_5607_: *mut crate::leanh::LeanObject,
    mut v_t_5608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5609_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0;
    v___x_5610_ = crate::leanh::lean_apply_1(v_inst_5606_, v_k_5607_);
    v___x_5611_ = crate::leanh::lean_box(0);
    v___x_5612_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(
        v___x_5610_,
        v___x_5611_,
        v___f_5609_,
        v_t_5608_,
    );
    return v___x_5612_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(
    mut v_00_u03b1_5613_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5614_: *mut crate::leanh::LeanObject,
    mut v_inst_5615_: *mut crate::leanh::LeanObject,
    mut v_k_5616_: *mut crate::leanh::LeanObject,
    mut v_t_5617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5618_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(
        v_inst_5615_,
        v_k_5616_,
        v_t_5617_,
    );
    return v___x_5618_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(
    mut v_x_5619_: *mut crate::leanh::LeanObject,
    mut v_x_5620_: *mut crate::leanh::LeanObject,
    mut v_h__1_5621_: *mut crate::leanh::LeanObject,
    mut v_h__2_5622_: *mut crate::leanh::LeanObject,
    mut v_h__3_5623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_5620_) {
        0 => {
            let mut v_a_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5623_);
            crate::leanh::lean_dec(v_h__2_5622_);
            v_a_5624_ = crate::leanh::lean_ctor_get(v_x_5620_, 0);
            crate::leanh::lean_inc(v_a_5624_);
            v_a_5625_ = crate::leanh::lean_ctor_get(v_x_5620_, 1);
            crate::leanh::lean_inc(v_a_5625_);
            v_a_5626_ = crate::leanh::lean_ctor_get(v_x_5620_, 2);
            crate::leanh::lean_inc(v_a_5626_);
            crate::leanh::lean_dec_ref_known(v_x_5620_, 3);
            v___x_5627_ = crate::leanh::lean_apply_5(
                v_h__1_5621_,
                v_x_5619_,
                v_a_5624_,
                crate::leanh::lean_box(0),
                v_a_5625_,
                v_a_5626_,
            );
            return v___x_5627_;
        }
        1 => {
            let mut v_a_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5623_);
            crate::leanh::lean_dec(v_h__1_5621_);
            v_a_5628_ = crate::leanh::lean_ctor_get(v_x_5620_, 0);
            crate::leanh::lean_inc(v_a_5628_);
            v_a_5629_ = crate::leanh::lean_ctor_get(v_x_5620_, 1);
            crate::leanh::lean_inc(v_a_5629_);
            v_a_5630_ = crate::leanh::lean_ctor_get(v_x_5620_, 2);
            crate::leanh::lean_inc(v_a_5630_);
            crate::leanh::lean_dec_ref_known(v_x_5620_, 3);
            v___x_5631_ = crate::leanh::lean_apply_4(
                v_h__2_5622_,
                v_x_5619_,
                v_a_5628_,
                v_a_5629_,
                v_a_5630_,
            );
            return v___x_5631_;
        }
        _ => {
            let mut v_a_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5622_);
            crate::leanh::lean_dec(v_h__1_5621_);
            v_a_5632_ = crate::leanh::lean_ctor_get(v_x_5620_, 0);
            crate::leanh::lean_inc(v_a_5632_);
            v_a_5633_ = crate::leanh::lean_ctor_get(v_x_5620_, 1);
            crate::leanh::lean_inc(v_a_5633_);
            v_a_5634_ = crate::leanh::lean_ctor_get(v_x_5620_, 2);
            crate::leanh::lean_inc(v_a_5634_);
            crate::leanh::lean_dec_ref_known(v_x_5620_, 3);
            v___x_5635_ = crate::leanh::lean_apply_5(
                v_h__3_5623_,
                v_x_5619_,
                v_a_5632_,
                v_a_5633_,
                crate::leanh::lean_box(0),
                v_a_5634_,
            );
            return v___x_5635_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(
    mut v_00_u03b1_5636_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5637_: *mut crate::leanh::LeanObject,
    mut v_inst_5638_: *mut crate::leanh::LeanObject,
    mut v_k_5639_: *mut crate::leanh::LeanObject,
    mut v_motive_5640_: *mut crate::leanh::LeanObject,
    mut v_x_5641_: *mut crate::leanh::LeanObject,
    mut v_x_5642_: *mut crate::leanh::LeanObject,
    mut v_h__1_5643_: *mut crate::leanh::LeanObject,
    mut v_h__2_5644_: *mut crate::leanh::LeanObject,
    mut v_h__3_5645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_5642_) {
        0 => {
            let mut v_a_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5645_);
            crate::leanh::lean_dec(v_h__2_5644_);
            v_a_5646_ = crate::leanh::lean_ctor_get(v_x_5642_, 0);
            crate::leanh::lean_inc(v_a_5646_);
            v_a_5647_ = crate::leanh::lean_ctor_get(v_x_5642_, 1);
            crate::leanh::lean_inc(v_a_5647_);
            v_a_5648_ = crate::leanh::lean_ctor_get(v_x_5642_, 2);
            crate::leanh::lean_inc(v_a_5648_);
            crate::leanh::lean_dec_ref_known(v_x_5642_, 3);
            v___x_5649_ = crate::leanh::lean_apply_5(
                v_h__1_5643_,
                v_x_5641_,
                v_a_5646_,
                crate::leanh::lean_box(0),
                v_a_5647_,
                v_a_5648_,
            );
            return v___x_5649_;
        }
        1 => {
            let mut v_a_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5645_);
            crate::leanh::lean_dec(v_h__1_5643_);
            v_a_5650_ = crate::leanh::lean_ctor_get(v_x_5642_, 0);
            crate::leanh::lean_inc(v_a_5650_);
            v_a_5651_ = crate::leanh::lean_ctor_get(v_x_5642_, 1);
            crate::leanh::lean_inc(v_a_5651_);
            v_a_5652_ = crate::leanh::lean_ctor_get(v_x_5642_, 2);
            crate::leanh::lean_inc(v_a_5652_);
            crate::leanh::lean_dec_ref_known(v_x_5642_, 3);
            v___x_5653_ = crate::leanh::lean_apply_4(
                v_h__2_5644_,
                v_x_5641_,
                v_a_5650_,
                v_a_5651_,
                v_a_5652_,
            );
            return v___x_5653_;
        }
        _ => {
            let mut v_a_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5644_);
            crate::leanh::lean_dec(v_h__1_5643_);
            v_a_5654_ = crate::leanh::lean_ctor_get(v_x_5642_, 0);
            crate::leanh::lean_inc(v_a_5654_);
            v_a_5655_ = crate::leanh::lean_ctor_get(v_x_5642_, 1);
            crate::leanh::lean_inc(v_a_5655_);
            v_a_5656_ = crate::leanh::lean_ctor_get(v_x_5642_, 2);
            crate::leanh::lean_inc(v_a_5656_);
            crate::leanh::lean_dec_ref_known(v_x_5642_, 3);
            v___x_5657_ = crate::leanh::lean_apply_5(
                v_h__3_5645_,
                v_x_5641_,
                v_a_5654_,
                v_a_5655_,
                crate::leanh::lean_box(0),
                v_a_5656_,
            );
            return v___x_5657_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(
    mut v_00_u03b1_5658_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5659_: *mut crate::leanh::LeanObject,
    mut v_inst_5660_: *mut crate::leanh::LeanObject,
    mut v_k_5661_: *mut crate::leanh::LeanObject,
    mut v_motive_5662_: *mut crate::leanh::LeanObject,
    mut v_x_5663_: *mut crate::leanh::LeanObject,
    mut v_x_5664_: *mut crate::leanh::LeanObject,
    mut v_h__1_5665_: *mut crate::leanh::LeanObject,
    mut v_h__2_5666_: *mut crate::leanh::LeanObject,
    mut v_h__3_5667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5668_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_5658_, v_00_u03b2_5659_, v_inst_5660_, v_k_5661_, v_motive_5662_, v_x_5663_, v_x_5664_, v_h__1_5665_, v_h__2_5666_, v_h__3_5667_);
    crate::leanh::lean_dec(v_k_5661_);
    crate::leanh::lean_dec_ref(v_inst_5660_);
    return v_res_5668_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(
    mut v_inst_5669_: *mut crate::leanh::LeanObject,
    mut v_k_5670_: *mut crate::leanh::LeanObject,
    mut v_k_x27_5671_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: u8 = 0;
    v___x_5672_ = crate::leanh::lean_apply_2(v_inst_5669_, v_k_5670_, v_k_x27_5671_);
    v___x_5673_ = (crate::leanh::lean_unbox(v___x_5672_) as u8);
    if v___x_5673_ == 1 {
        let mut v___x_5674_: u8 = 0;
        v___x_5674_ = 2;
        return v___x_5674_;
    } else {
        let mut v___x_5675_: u8 = 0;
        v___x_5675_ = (crate::leanh::lean_unbox(v___x_5672_) as u8);
        return v___x_5675_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(
    mut v_inst_5676_: *mut crate::leanh::LeanObject,
    mut v_k_5677_: *mut crate::leanh::LeanObject,
    mut v_k_x27_5678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5679_: u8 = 0;
    let mut v_r_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5679_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(
        v_inst_5676_,
        v_k_5677_,
        v_k_x27_5678_,
    );
    v_r_5680_ = crate::leanh::lean_box((v_res_5679_) as usize);
    return v_r_5680_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(
    mut v_inst_5681_: *mut crate::leanh::LeanObject,
    mut v_k_5682_: *mut crate::leanh::LeanObject,
    mut v_t_5683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5684_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5684_, 0, v_inst_5681_);
    crate::leanh::lean_closure_set(v___f_5684_, 1, v_k_5682_);
    v___f_5685_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0;
    v___x_5686_ =
        l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_5684_, v_t_5683_, v___f_5685_);
    return v___x_5686_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(
    mut v_00_u03b1_5687_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5688_: *mut crate::leanh::LeanObject,
    mut v_inst_5689_: *mut crate::leanh::LeanObject,
    mut v_k_5690_: *mut crate::leanh::LeanObject,
    mut v_t_5691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5692_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(
        v_inst_5689_,
        v_k_5690_,
        v_t_5691_,
    );
    return v___x_5692_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(
    mut v_x_5693_: *mut crate::leanh::LeanObject,
    mut v_x_5694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_5694_) {
        0 => {
            let mut v_a_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5695_ = crate::leanh::lean_ctor_get(v_x_5694_, 0);
            v_a_5696_ = crate::leanh::lean_ctor_get(v_x_5694_, 1);
            crate::leanh::lean_inc(v_a_5696_);
            crate::leanh::lean_inc(v_a_5695_);
            v___x_5697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5697_, 0, v_a_5695_);
            crate::leanh::lean_ctor_set(v___x_5697_, 1, v_a_5696_);
            v___x_5698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5698_, 0, v___x_5697_);
            return v___x_5698_;
        }
        1 => {
            let mut v_a_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5699_ = crate::leanh::lean_ctor_get(v_x_5694_, 2);
            v___x_5700_ = l_List_head_x3f___redArg(v_a_5699_);
            if crate::leanh::lean_obj_tag(v___x_5700_) == 0 {
                crate::leanh::lean_inc(v_x_5693_);
                return v_x_5693_;
            } else {
                return v___x_5700_;
            }
        }
        _ => {
            crate::leanh::lean_inc(v_x_5693_);
            return v_x_5693_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(
    mut v_x_5701_: *mut crate::leanh::LeanObject,
    mut v_x_5702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5703_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(
        v_x_5701_, v_x_5702_,
    );
    crate::leanh::lean_dec_ref(v_x_5702_);
    crate::leanh::lean_dec(v_x_5701_);
    return v_res_5703_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(
    mut v_inst_5705_: *mut crate::leanh::LeanObject,
    mut v_k_5706_: *mut crate::leanh::LeanObject,
    mut v_t_5707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5708_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5708_, 0, v_inst_5705_);
    crate::leanh::lean_closure_set(v___f_5708_, 1, v_k_5706_);
    v___f_5709_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0;
    v___x_5710_ = crate::leanh::lean_box(0);
    v___x_5711_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(
        v___f_5708_,
        v___x_5710_,
        v___f_5709_,
        v_t_5707_,
    );
    return v___x_5711_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(
    mut v_00_u03b1_5712_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5713_: *mut crate::leanh::LeanObject,
    mut v_inst_5714_: *mut crate::leanh::LeanObject,
    mut v_k_5715_: *mut crate::leanh::LeanObject,
    mut v_t_5716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5717_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(
        v_inst_5714_,
        v_k_5715_,
        v_t_5716_,
    );
    return v___x_5717_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(
    mut v_x_5718_: u8,
    mut v_h__1_5719_: *mut crate::leanh::LeanObject,
    mut v_h__2_5720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_5718_ == 0 {
        let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5720_);
        v___x_5721_ = crate::leanh::lean_box(0);
        v___x_5722_ = crate::leanh::lean_apply_1(v_h__1_5719_, v___x_5721_);
        return v___x_5722_;
    } else {
        let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5719_);
        v___x_5723_ = crate::leanh::lean_box((v_x_5718_) as usize);
        v___x_5724_ =
            crate::leanh::lean_apply_2(v_h__2_5720_, v___x_5723_, crate::leanh::lean_box(0));
        return v___x_5724_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(
    mut v_x_5725_: *mut crate::leanh::LeanObject,
    mut v_h__1_5726_: *mut crate::leanh::LeanObject,
    mut v_h__2_5727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_5728_: u8 = 0;
    let mut v_res_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_5728_ = (crate::leanh::lean_unbox(v_x_5725_) as u8);
    v_res_5729_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_5728_, v_h__1_5726_, v_h__2_5727_);
    return v_res_5729_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(
    mut v_motive_5730_: *mut crate::leanh::LeanObject,
    mut v_x_5731_: u8,
    mut v_h__1_5732_: *mut crate::leanh::LeanObject,
    mut v_h__2_5733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_5731_ == 0 {
        let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5733_);
        v___x_5734_ = crate::leanh::lean_box(0);
        v___x_5735_ = crate::leanh::lean_apply_1(v_h__1_5732_, v___x_5734_);
        return v___x_5735_;
    } else {
        let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5732_);
        v___x_5736_ = crate::leanh::lean_box((v_x_5731_) as usize);
        v___x_5737_ =
            crate::leanh::lean_apply_2(v_h__2_5733_, v___x_5736_, crate::leanh::lean_box(0));
        return v___x_5737_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(
    mut v_motive_5738_: *mut crate::leanh::LeanObject,
    mut v_x_5739_: *mut crate::leanh::LeanObject,
    mut v_h__1_5740_: *mut crate::leanh::LeanObject,
    mut v_h__2_5741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_28__boxed_5742_: u8 = 0;
    let mut v_res_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_28__boxed_5742_ = (crate::leanh::lean_unbox(v_x_5739_) as u8);
    v_res_5743_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_5738_, v_x_28__boxed_5742_, v_h__1_5740_, v_h__2_5741_);
    return v_res_5743_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(
    mut v_x_5744_: *mut crate::leanh::LeanObject,
    mut v_x_5745_: *mut crate::leanh::LeanObject,
    mut v_h__1_5746_: *mut crate::leanh::LeanObject,
    mut v_h__2_5747_: *mut crate::leanh::LeanObject,
    mut v_h__3_5748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_5745_) {
        0 => {
            let mut v_a_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5748_);
            crate::leanh::lean_dec(v_h__2_5747_);
            v_a_5749_ = crate::leanh::lean_ctor_get(v_x_5745_, 0);
            crate::leanh::lean_inc(v_a_5749_);
            v_a_5750_ = crate::leanh::lean_ctor_get(v_x_5745_, 1);
            crate::leanh::lean_inc(v_a_5750_);
            v_a_5751_ = crate::leanh::lean_ctor_get(v_x_5745_, 2);
            crate::leanh::lean_inc(v_a_5751_);
            crate::leanh::lean_dec_ref_known(v_x_5745_, 3);
            v___x_5752_ = crate::leanh::lean_apply_5(
                v_h__1_5746_,
                v_x_5744_,
                v_a_5749_,
                crate::leanh::lean_box(0),
                v_a_5750_,
                v_a_5751_,
            );
            return v___x_5752_;
        }
        1 => {
            let mut v_a_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5748_);
            crate::leanh::lean_dec(v_h__1_5746_);
            v_a_5753_ = crate::leanh::lean_ctor_get(v_x_5745_, 0);
            crate::leanh::lean_inc(v_a_5753_);
            v_a_5754_ = crate::leanh::lean_ctor_get(v_x_5745_, 1);
            crate::leanh::lean_inc(v_a_5754_);
            v_a_5755_ = crate::leanh::lean_ctor_get(v_x_5745_, 2);
            crate::leanh::lean_inc(v_a_5755_);
            crate::leanh::lean_dec_ref_known(v_x_5745_, 3);
            v___x_5756_ = crate::leanh::lean_apply_4(
                v_h__2_5747_,
                v_x_5744_,
                v_a_5753_,
                v_a_5754_,
                v_a_5755_,
            );
            return v___x_5756_;
        }
        _ => {
            let mut v_a_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5747_);
            crate::leanh::lean_dec(v_h__1_5746_);
            v_a_5757_ = crate::leanh::lean_ctor_get(v_x_5745_, 0);
            crate::leanh::lean_inc(v_a_5757_);
            v_a_5758_ = crate::leanh::lean_ctor_get(v_x_5745_, 1);
            crate::leanh::lean_inc(v_a_5758_);
            v_a_5759_ = crate::leanh::lean_ctor_get(v_x_5745_, 2);
            crate::leanh::lean_inc(v_a_5759_);
            crate::leanh::lean_dec_ref_known(v_x_5745_, 3);
            v___x_5760_ = crate::leanh::lean_apply_5(
                v_h__3_5748_,
                v_x_5744_,
                v_a_5757_,
                v_a_5758_,
                crate::leanh::lean_box(0),
                v_a_5759_,
            );
            return v___x_5760_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(
    mut v_00_u03b1_5761_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5762_: *mut crate::leanh::LeanObject,
    mut v_inst_5763_: *mut crate::leanh::LeanObject,
    mut v_k_5764_: *mut crate::leanh::LeanObject,
    mut v_motive_5765_: *mut crate::leanh::LeanObject,
    mut v_x_5766_: *mut crate::leanh::LeanObject,
    mut v_x_5767_: *mut crate::leanh::LeanObject,
    mut v_h__1_5768_: *mut crate::leanh::LeanObject,
    mut v_h__2_5769_: *mut crate::leanh::LeanObject,
    mut v_h__3_5770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_5767_) {
        0 => {
            let mut v_a_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5770_);
            crate::leanh::lean_dec(v_h__2_5769_);
            v_a_5771_ = crate::leanh::lean_ctor_get(v_x_5767_, 0);
            crate::leanh::lean_inc(v_a_5771_);
            v_a_5772_ = crate::leanh::lean_ctor_get(v_x_5767_, 1);
            crate::leanh::lean_inc(v_a_5772_);
            v_a_5773_ = crate::leanh::lean_ctor_get(v_x_5767_, 2);
            crate::leanh::lean_inc(v_a_5773_);
            crate::leanh::lean_dec_ref_known(v_x_5767_, 3);
            v___x_5774_ = crate::leanh::lean_apply_5(
                v_h__1_5768_,
                v_x_5766_,
                v_a_5771_,
                crate::leanh::lean_box(0),
                v_a_5772_,
                v_a_5773_,
            );
            return v___x_5774_;
        }
        1 => {
            let mut v_a_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5770_);
            crate::leanh::lean_dec(v_h__1_5768_);
            v_a_5775_ = crate::leanh::lean_ctor_get(v_x_5767_, 0);
            crate::leanh::lean_inc(v_a_5775_);
            v_a_5776_ = crate::leanh::lean_ctor_get(v_x_5767_, 1);
            crate::leanh::lean_inc(v_a_5776_);
            v_a_5777_ = crate::leanh::lean_ctor_get(v_x_5767_, 2);
            crate::leanh::lean_inc(v_a_5777_);
            crate::leanh::lean_dec_ref_known(v_x_5767_, 3);
            v___x_5778_ = crate::leanh::lean_apply_4(
                v_h__2_5769_,
                v_x_5766_,
                v_a_5775_,
                v_a_5776_,
                v_a_5777_,
            );
            return v___x_5778_;
        }
        _ => {
            let mut v_a_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5769_);
            crate::leanh::lean_dec(v_h__1_5768_);
            v_a_5779_ = crate::leanh::lean_ctor_get(v_x_5767_, 0);
            crate::leanh::lean_inc(v_a_5779_);
            v_a_5780_ = crate::leanh::lean_ctor_get(v_x_5767_, 1);
            crate::leanh::lean_inc(v_a_5780_);
            v_a_5781_ = crate::leanh::lean_ctor_get(v_x_5767_, 2);
            crate::leanh::lean_inc(v_a_5781_);
            crate::leanh::lean_dec_ref_known(v_x_5767_, 3);
            v___x_5782_ = crate::leanh::lean_apply_5(
                v_h__3_5770_,
                v_x_5766_,
                v_a_5779_,
                v_a_5780_,
                crate::leanh::lean_box(0),
                v_a_5781_,
            );
            return v___x_5782_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(
    mut v_00_u03b1_5783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5784_: *mut crate::leanh::LeanObject,
    mut v_inst_5785_: *mut crate::leanh::LeanObject,
    mut v_k_5786_: *mut crate::leanh::LeanObject,
    mut v_motive_5787_: *mut crate::leanh::LeanObject,
    mut v_x_5788_: *mut crate::leanh::LeanObject,
    mut v_x_5789_: *mut crate::leanh::LeanObject,
    mut v_h__1_5790_: *mut crate::leanh::LeanObject,
    mut v_h__2_5791_: *mut crate::leanh::LeanObject,
    mut v_h__3_5792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5793_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_5783_, v_00_u03b2_5784_, v_inst_5785_, v_k_5786_, v_motive_5787_, v_x_5788_, v_x_5789_, v_h__1_5790_, v_h__2_5791_, v_h__3_5792_);
    crate::leanh::lean_dec(v_k_5786_);
    crate::leanh::lean_dec_ref(v_inst_5785_);
    return v_res_5793_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(
    mut v_x_5794_: u8,
    mut v_h__1_5795_: *mut crate::leanh::LeanObject,
    mut v_h__2_5796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_5794_ == 2 {
        let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5796_);
        v___x_5797_ = crate::leanh::lean_box(0);
        v___x_5798_ = crate::leanh::lean_apply_1(v_h__1_5795_, v___x_5797_);
        return v___x_5798_;
    } else {
        let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5795_);
        v___x_5799_ = crate::leanh::lean_box((v_x_5794_) as usize);
        v___x_5800_ =
            crate::leanh::lean_apply_2(v_h__2_5796_, v___x_5799_, crate::leanh::lean_box(0));
        return v___x_5800_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(
    mut v_x_5801_: *mut crate::leanh::LeanObject,
    mut v_h__1_5802_: *mut crate::leanh::LeanObject,
    mut v_h__2_5803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_5804_: u8 = 0;
    let mut v_res_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_5804_ = (crate::leanh::lean_unbox(v_x_5801_) as u8);
    v_res_5805_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_5804_, v_h__1_5802_, v_h__2_5803_);
    return v_res_5805_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(
    mut v_motive_5806_: *mut crate::leanh::LeanObject,
    mut v_x_5807_: u8,
    mut v_h__1_5808_: *mut crate::leanh::LeanObject,
    mut v_h__2_5809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_5807_ == 2 {
        let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5809_);
        v___x_5810_ = crate::leanh::lean_box(0);
        v___x_5811_ = crate::leanh::lean_apply_1(v_h__1_5808_, v___x_5810_);
        return v___x_5811_;
    } else {
        let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5808_);
        v___x_5812_ = crate::leanh::lean_box((v_x_5807_) as usize);
        v___x_5813_ =
            crate::leanh::lean_apply_2(v_h__2_5809_, v___x_5812_, crate::leanh::lean_box(0));
        return v___x_5813_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(
    mut v_motive_5814_: *mut crate::leanh::LeanObject,
    mut v_x_5815_: *mut crate::leanh::LeanObject,
    mut v_h__1_5816_: *mut crate::leanh::LeanObject,
    mut v_h__2_5817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_28__boxed_5818_: u8 = 0;
    let mut v_res_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_28__boxed_5818_ = (crate::leanh::lean_unbox(v_x_5815_) as u8);
    v_res_5819_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_5814_, v_x_28__boxed_5818_, v_h__1_5816_, v_h__2_5817_);
    return v_res_5819_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(
    mut v_x_5820_: u8,
    mut v_h__1_5821_: *mut crate::leanh::LeanObject,
    mut v_h__2_5822_: *mut crate::leanh::LeanObject,
    mut v_h__3_5823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5820_ {
        0 => {
            let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5823_);
            crate::leanh::lean_dec(v_h__2_5822_);
            v___x_5824_ = crate::leanh::lean_box(0);
            v___x_5825_ = crate::leanh::lean_apply_1(v_h__1_5821_, v___x_5824_);
            return v___x_5825_;
        }
        1 => {
            let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5823_);
            crate::leanh::lean_dec(v_h__1_5821_);
            v___x_5826_ = crate::leanh::lean_box(0);
            v___x_5827_ = crate::leanh::lean_apply_1(v_h__2_5822_, v___x_5826_);
            return v___x_5827_;
        }
        _ => {
            let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5822_);
            crate::leanh::lean_dec(v_h__1_5821_);
            v___x_5828_ = crate::leanh::lean_box(0);
            v___x_5829_ = crate::leanh::lean_apply_1(v_h__3_5823_, v___x_5828_);
            return v___x_5829_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(
    mut v_x_5830_: *mut crate::leanh::LeanObject,
    mut v_h__1_5831_: *mut crate::leanh::LeanObject,
    mut v_h__2_5832_: *mut crate::leanh::LeanObject,
    mut v_h__3_5833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_5834_: u8 = 0;
    let mut v_res_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_5834_ = (crate::leanh::lean_unbox(v_x_5830_) as u8);
    v_res_5835_ =
        l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(
            v_x_36__boxed_5834_,
            v_h__1_5831_,
            v_h__2_5832_,
            v_h__3_5833_,
        );
    return v_res_5835_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(
    mut v_motive_5836_: *mut crate::leanh::LeanObject,
    mut v_x_5837_: u8,
    mut v_h__1_5838_: *mut crate::leanh::LeanObject,
    mut v_h__2_5839_: *mut crate::leanh::LeanObject,
    mut v_h__3_5840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5837_ {
        0 => {
            let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5840_);
            crate::leanh::lean_dec(v_h__2_5839_);
            v___x_5841_ = crate::leanh::lean_box(0);
            v___x_5842_ = crate::leanh::lean_apply_1(v_h__1_5838_, v___x_5841_);
            return v___x_5842_;
        }
        1 => {
            let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5840_);
            crate::leanh::lean_dec(v_h__1_5838_);
            v___x_5843_ = crate::leanh::lean_box(0);
            v___x_5844_ = crate::leanh::lean_apply_1(v_h__2_5839_, v___x_5843_);
            return v___x_5844_;
        }
        _ => {
            let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5839_);
            crate::leanh::lean_dec(v_h__1_5838_);
            v___x_5845_ = crate::leanh::lean_box(0);
            v___x_5846_ = crate::leanh::lean_apply_1(v_h__3_5840_, v___x_5845_);
            return v___x_5846_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(
    mut v_motive_5847_: *mut crate::leanh::LeanObject,
    mut v_x_5848_: *mut crate::leanh::LeanObject,
    mut v_h__1_5849_: *mut crate::leanh::LeanObject,
    mut v_h__2_5850_: *mut crate::leanh::LeanObject,
    mut v_h__3_5851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_5852_: u8 = 0;
    let mut v_res_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_5852_ = (crate::leanh::lean_unbox(v_x_5848_) as u8);
    v_res_5853_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter(
        v_motive_5847_,
        v_x_51__boxed_5852_,
        v_h__1_5849_,
        v_h__2_5850_,
        v_h__3_5851_,
    );
    return v_res_5853_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___redArg(
    mut v_x_5854_: *mut crate::leanh::LeanObject,
    mut v_h__1_5855_: *mut crate::leanh::LeanObject,
    mut v_h__2_5856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5854_) == 0 {
        let mut v_size_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5855_);
        v_size_5857_ = crate::leanh::lean_ctor_get(v_x_5854_, 0);
        crate::leanh::lean_inc(v_size_5857_);
        v_k_5858_ = crate::leanh::lean_ctor_get(v_x_5854_, 1);
        crate::leanh::lean_inc(v_k_5858_);
        v_v_5859_ = crate::leanh::lean_ctor_get(v_x_5854_, 2);
        crate::leanh::lean_inc(v_v_5859_);
        v_l_5860_ = crate::leanh::lean_ctor_get(v_x_5854_, 3);
        crate::leanh::lean_inc(v_l_5860_);
        v_r_5861_ = crate::leanh::lean_ctor_get(v_x_5854_, 4);
        crate::leanh::lean_inc(v_r_5861_);
        crate::leanh::lean_dec_ref_known(v_x_5854_, 5);
        v___x_5862_ = crate::leanh::lean_apply_7(
            v_h__2_5856_,
            v_size_5857_,
            v_k_5858_,
            v_v_5859_,
            v_l_5860_,
            v_r_5861_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5862_;
    } else {
        let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5856_);
        v___x_5863_ = crate::leanh::lean_apply_2(
            v_h__1_5855_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5863_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(
    mut v_00_u03b1_5864_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5865_: *mut crate::leanh::LeanObject,
    mut v_inst_5866_: *mut crate::leanh::LeanObject,
    mut v_k_5867_: *mut crate::leanh::LeanObject,
    mut v_motive_5868_: *mut crate::leanh::LeanObject,
    mut v_x_5869_: *mut crate::leanh::LeanObject,
    mut v_x_5870_: *mut crate::leanh::LeanObject,
    mut v_x_5871_: *mut crate::leanh::LeanObject,
    mut v_h__1_5872_: *mut crate::leanh::LeanObject,
    mut v_h__2_5873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5869_) == 0 {
        let mut v_size_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5872_);
        v_size_5874_ = crate::leanh::lean_ctor_get(v_x_5869_, 0);
        crate::leanh::lean_inc(v_size_5874_);
        v_k_5875_ = crate::leanh::lean_ctor_get(v_x_5869_, 1);
        crate::leanh::lean_inc(v_k_5875_);
        v_v_5876_ = crate::leanh::lean_ctor_get(v_x_5869_, 2);
        crate::leanh::lean_inc(v_v_5876_);
        v_l_5877_ = crate::leanh::lean_ctor_get(v_x_5869_, 3);
        crate::leanh::lean_inc(v_l_5877_);
        v_r_5878_ = crate::leanh::lean_ctor_get(v_x_5869_, 4);
        crate::leanh::lean_inc(v_r_5878_);
        crate::leanh::lean_dec_ref_known(v_x_5869_, 5);
        v___x_5879_ = crate::leanh::lean_apply_7(
            v_h__2_5873_,
            v_size_5874_,
            v_k_5875_,
            v_v_5876_,
            v_l_5877_,
            v_r_5878_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5879_;
    } else {
        let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5873_);
        v___x_5880_ = crate::leanh::lean_apply_2(
            v_h__1_5872_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5880_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(
    mut v_00_u03b1_5881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5882_: *mut crate::leanh::LeanObject,
    mut v_inst_5883_: *mut crate::leanh::LeanObject,
    mut v_k_5884_: *mut crate::leanh::LeanObject,
    mut v_motive_5885_: *mut crate::leanh::LeanObject,
    mut v_x_5886_: *mut crate::leanh::LeanObject,
    mut v_x_5887_: *mut crate::leanh::LeanObject,
    mut v_x_5888_: *mut crate::leanh::LeanObject,
    mut v_h__1_5889_: *mut crate::leanh::LeanObject,
    mut v_h__2_5890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5891_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(v_00_u03b1_5881_, v_00_u03b2_5882_, v_inst_5883_, v_k_5884_, v_motive_5885_, v_x_5886_, v_x_5887_, v_x_5888_, v_h__1_5889_, v_h__2_5890_);
    crate::leanh::lean_dec(v_k_5884_);
    crate::leanh::lean_dec_ref(v_inst_5883_);
    return v_res_5891_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(
    mut v_x_5892_: *mut crate::leanh::LeanObject,
    mut v_h__1_5893_: *mut crate::leanh::LeanObject,
    mut v_h__2_5894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5892_) == 0 {
        let mut v_size_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5893_);
        v_size_5895_ = crate::leanh::lean_ctor_get(v_x_5892_, 0);
        crate::leanh::lean_inc(v_size_5895_);
        v_k_5896_ = crate::leanh::lean_ctor_get(v_x_5892_, 1);
        crate::leanh::lean_inc(v_k_5896_);
        v_v_5897_ = crate::leanh::lean_ctor_get(v_x_5892_, 2);
        crate::leanh::lean_inc(v_v_5897_);
        v_l_5898_ = crate::leanh::lean_ctor_get(v_x_5892_, 3);
        crate::leanh::lean_inc(v_l_5898_);
        v_r_5899_ = crate::leanh::lean_ctor_get(v_x_5892_, 4);
        crate::leanh::lean_inc(v_r_5899_);
        crate::leanh::lean_dec_ref_known(v_x_5892_, 5);
        v___x_5900_ = crate::leanh::lean_apply_7(
            v_h__2_5894_,
            v_size_5895_,
            v_k_5896_,
            v_v_5897_,
            v_l_5898_,
            v_r_5899_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5900_;
    } else {
        let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5894_);
        v___x_5901_ = crate::leanh::lean_apply_2(
            v_h__1_5893_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5901_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(
    mut v_00_u03b1_5902_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5903_: *mut crate::leanh::LeanObject,
    mut v_inst_5904_: *mut crate::leanh::LeanObject,
    mut v_k_5905_: *mut crate::leanh::LeanObject,
    mut v_motive_5906_: *mut crate::leanh::LeanObject,
    mut v_x_5907_: *mut crate::leanh::LeanObject,
    mut v_x_5908_: *mut crate::leanh::LeanObject,
    mut v_x_5909_: *mut crate::leanh::LeanObject,
    mut v_h__1_5910_: *mut crate::leanh::LeanObject,
    mut v_h__2_5911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5907_) == 0 {
        let mut v_size_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5910_);
        v_size_5912_ = crate::leanh::lean_ctor_get(v_x_5907_, 0);
        crate::leanh::lean_inc(v_size_5912_);
        v_k_5913_ = crate::leanh::lean_ctor_get(v_x_5907_, 1);
        crate::leanh::lean_inc(v_k_5913_);
        v_v_5914_ = crate::leanh::lean_ctor_get(v_x_5907_, 2);
        crate::leanh::lean_inc(v_v_5914_);
        v_l_5915_ = crate::leanh::lean_ctor_get(v_x_5907_, 3);
        crate::leanh::lean_inc(v_l_5915_);
        v_r_5916_ = crate::leanh::lean_ctor_get(v_x_5907_, 4);
        crate::leanh::lean_inc(v_r_5916_);
        crate::leanh::lean_dec_ref_known(v_x_5907_, 5);
        v___x_5917_ = crate::leanh::lean_apply_7(
            v_h__2_5911_,
            v_size_5912_,
            v_k_5913_,
            v_v_5914_,
            v_l_5915_,
            v_r_5916_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5917_;
    } else {
        let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5911_);
        v___x_5918_ = crate::leanh::lean_apply_2(
            v_h__1_5910_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5918_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(
    mut v_00_u03b1_5919_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5920_: *mut crate::leanh::LeanObject,
    mut v_inst_5921_: *mut crate::leanh::LeanObject,
    mut v_k_5922_: *mut crate::leanh::LeanObject,
    mut v_motive_5923_: *mut crate::leanh::LeanObject,
    mut v_x_5924_: *mut crate::leanh::LeanObject,
    mut v_x_5925_: *mut crate::leanh::LeanObject,
    mut v_x_5926_: *mut crate::leanh::LeanObject,
    mut v_h__1_5927_: *mut crate::leanh::LeanObject,
    mut v_h__2_5928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5929_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(v_00_u03b1_5919_, v_00_u03b2_5920_, v_inst_5921_, v_k_5922_, v_motive_5923_, v_x_5924_, v_x_5925_, v_x_5926_, v_h__1_5927_, v_h__2_5928_);
    crate::leanh::lean_dec(v_k_5922_);
    crate::leanh::lean_dec_ref(v_inst_5921_);
    return v_res_5929_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(
    mut v_x_5930_: *mut crate::leanh::LeanObject,
    mut v_h__1_5931_: *mut crate::leanh::LeanObject,
    mut v_h__2_5932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5930_) == 0 {
        let mut v_size_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5931_);
        v_size_5933_ = crate::leanh::lean_ctor_get(v_x_5930_, 0);
        crate::leanh::lean_inc(v_size_5933_);
        v_k_5934_ = crate::leanh::lean_ctor_get(v_x_5930_, 1);
        crate::leanh::lean_inc(v_k_5934_);
        v_v_5935_ = crate::leanh::lean_ctor_get(v_x_5930_, 2);
        crate::leanh::lean_inc(v_v_5935_);
        v_l_5936_ = crate::leanh::lean_ctor_get(v_x_5930_, 3);
        crate::leanh::lean_inc(v_l_5936_);
        v_r_5937_ = crate::leanh::lean_ctor_get(v_x_5930_, 4);
        crate::leanh::lean_inc(v_r_5937_);
        crate::leanh::lean_dec_ref_known(v_x_5930_, 5);
        v___x_5938_ = crate::leanh::lean_apply_7(
            v_h__2_5932_,
            v_size_5933_,
            v_k_5934_,
            v_v_5935_,
            v_l_5936_,
            v_r_5937_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5938_;
    } else {
        let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5932_);
        v___x_5939_ = crate::leanh::lean_apply_2(
            v_h__1_5931_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5939_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(
    mut v_00_u03b1_5940_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5941_: *mut crate::leanh::LeanObject,
    mut v_inst_5942_: *mut crate::leanh::LeanObject,
    mut v_k_5943_: *mut crate::leanh::LeanObject,
    mut v_motive_5944_: *mut crate::leanh::LeanObject,
    mut v_x_5945_: *mut crate::leanh::LeanObject,
    mut v_x_5946_: *mut crate::leanh::LeanObject,
    mut v_x_5947_: *mut crate::leanh::LeanObject,
    mut v_h__1_5948_: *mut crate::leanh::LeanObject,
    mut v_h__2_5949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5945_) == 0 {
        let mut v_size_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5948_);
        v_size_5950_ = crate::leanh::lean_ctor_get(v_x_5945_, 0);
        crate::leanh::lean_inc(v_size_5950_);
        v_k_5951_ = crate::leanh::lean_ctor_get(v_x_5945_, 1);
        crate::leanh::lean_inc(v_k_5951_);
        v_v_5952_ = crate::leanh::lean_ctor_get(v_x_5945_, 2);
        crate::leanh::lean_inc(v_v_5952_);
        v_l_5953_ = crate::leanh::lean_ctor_get(v_x_5945_, 3);
        crate::leanh::lean_inc(v_l_5953_);
        v_r_5954_ = crate::leanh::lean_ctor_get(v_x_5945_, 4);
        crate::leanh::lean_inc(v_r_5954_);
        crate::leanh::lean_dec_ref_known(v_x_5945_, 5);
        v___x_5955_ = crate::leanh::lean_apply_7(
            v_h__2_5949_,
            v_size_5950_,
            v_k_5951_,
            v_v_5952_,
            v_l_5953_,
            v_r_5954_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5955_;
    } else {
        let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5949_);
        v___x_5956_ = crate::leanh::lean_apply_2(
            v_h__1_5948_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5956_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(
    mut v_00_u03b1_5957_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5958_: *mut crate::leanh::LeanObject,
    mut v_inst_5959_: *mut crate::leanh::LeanObject,
    mut v_k_5960_: *mut crate::leanh::LeanObject,
    mut v_motive_5961_: *mut crate::leanh::LeanObject,
    mut v_x_5962_: *mut crate::leanh::LeanObject,
    mut v_x_5963_: *mut crate::leanh::LeanObject,
    mut v_x_5964_: *mut crate::leanh::LeanObject,
    mut v_h__1_5965_: *mut crate::leanh::LeanObject,
    mut v_h__2_5966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5967_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(v_00_u03b1_5957_, v_00_u03b2_5958_, v_inst_5959_, v_k_5960_, v_motive_5961_, v_x_5962_, v_x_5963_, v_x_5964_, v_h__1_5965_, v_h__2_5966_);
    crate::leanh::lean_dec(v_k_5960_);
    crate::leanh::lean_dec_ref(v_inst_5959_);
    return v_res_5967_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(
    mut v_x_5968_: u8,
    mut v_h__1_5969_: *mut crate::leanh::LeanObject,
    mut v_h__2_5970_: *mut crate::leanh::LeanObject,
    mut v_h__3_5971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5968_ {
        0 => {
            let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5970_);
            crate::leanh::lean_dec(v_h__1_5969_);
            v___x_5972_ = crate::leanh::lean_apply_1(v_h__3_5971_, crate::leanh::lean_box(0));
            return v___x_5972_;
        }
        1 => {
            let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5971_);
            crate::leanh::lean_dec(v_h__1_5969_);
            v___x_5973_ = crate::leanh::lean_apply_1(v_h__2_5970_, crate::leanh::lean_box(0));
            return v___x_5973_;
        }
        _ => {
            let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5971_);
            crate::leanh::lean_dec(v_h__2_5970_);
            v___x_5974_ = crate::leanh::lean_apply_1(v_h__1_5969_, crate::leanh::lean_box(0));
            return v___x_5974_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(
    mut v_x_5975_: *mut crate::leanh::LeanObject,
    mut v_h__1_5976_: *mut crate::leanh::LeanObject,
    mut v_h__2_5977_: *mut crate::leanh::LeanObject,
    mut v_h__3_5978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_5979_: u8 = 0;
    let mut v_res_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_5979_ = (crate::leanh::lean_unbox(v_x_5975_) as u8);
    v_res_5980_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_33__boxed_5979_, v_h__1_5976_, v_h__2_5977_, v_h__3_5978_);
    return v_res_5980_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(
    mut v_motive_5981_: *mut crate::leanh::LeanObject,
    mut v_x_5982_: u8,
    mut v_h__1_5983_: *mut crate::leanh::LeanObject,
    mut v_h__2_5984_: *mut crate::leanh::LeanObject,
    mut v_h__3_5985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_5982_ {
        0 => {
            let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_5984_);
            crate::leanh::lean_dec(v_h__1_5983_);
            v___x_5986_ = crate::leanh::lean_apply_1(v_h__3_5985_, crate::leanh::lean_box(0));
            return v___x_5986_;
        }
        1 => {
            let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5985_);
            crate::leanh::lean_dec(v_h__1_5983_);
            v___x_5987_ = crate::leanh::lean_apply_1(v_h__2_5984_, crate::leanh::lean_box(0));
            return v___x_5987_;
        }
        _ => {
            let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5985_);
            crate::leanh::lean_dec(v_h__2_5984_);
            v___x_5988_ = crate::leanh::lean_apply_1(v_h__1_5983_, crate::leanh::lean_box(0));
            return v___x_5988_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(
    mut v_motive_5989_: *mut crate::leanh::LeanObject,
    mut v_x_5990_: *mut crate::leanh::LeanObject,
    mut v_h__1_5991_: *mut crate::leanh::LeanObject,
    mut v_h__2_5992_: *mut crate::leanh::LeanObject,
    mut v_h__3_5993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42__boxed_5994_: u8 = 0;
    let mut v_res_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_5994_ = (crate::leanh::lean_unbox(v_x_5990_) as u8);
    v_res_5995_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_5989_, v_x_42__boxed_5994_, v_h__1_5991_, v_h__2_5992_, v_h__3_5993_);
    return v_res_5995_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(
    mut v_x_5996_: *mut crate::leanh::LeanObject,
    mut v_h__1_5997_: *mut crate::leanh::LeanObject,
    mut v_h__2_5998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5996_) == 0 {
        let mut v_size_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5997_);
        v_size_5999_ = crate::leanh::lean_ctor_get(v_x_5996_, 0);
        crate::leanh::lean_inc(v_size_5999_);
        v_k_6000_ = crate::leanh::lean_ctor_get(v_x_5996_, 1);
        crate::leanh::lean_inc(v_k_6000_);
        v_v_6001_ = crate::leanh::lean_ctor_get(v_x_5996_, 2);
        crate::leanh::lean_inc(v_v_6001_);
        v_l_6002_ = crate::leanh::lean_ctor_get(v_x_5996_, 3);
        crate::leanh::lean_inc(v_l_6002_);
        v_r_6003_ = crate::leanh::lean_ctor_get(v_x_5996_, 4);
        crate::leanh::lean_inc(v_r_6003_);
        crate::leanh::lean_dec_ref_known(v_x_5996_, 5);
        v___x_6004_ = crate::leanh::lean_apply_7(
            v_h__2_5998_,
            v_size_5999_,
            v_k_6000_,
            v_v_6001_,
            v_l_6002_,
            v_r_6003_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6004_;
    } else {
        let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5998_);
        v___x_6005_ = crate::leanh::lean_apply_2(
            v_h__1_5997_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6005_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(
    mut v_00_u03b1_6006_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6007_: *mut crate::leanh::LeanObject,
    mut v_inst_6008_: *mut crate::leanh::LeanObject,
    mut v_k_6009_: *mut crate::leanh::LeanObject,
    mut v_motive_6010_: *mut crate::leanh::LeanObject,
    mut v_x_6011_: *mut crate::leanh::LeanObject,
    mut v_x_6012_: *mut crate::leanh::LeanObject,
    mut v_x_6013_: *mut crate::leanh::LeanObject,
    mut v_h__1_6014_: *mut crate::leanh::LeanObject,
    mut v_h__2_6015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6011_) == 0 {
        let mut v_size_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6014_);
        v_size_6016_ = crate::leanh::lean_ctor_get(v_x_6011_, 0);
        crate::leanh::lean_inc(v_size_6016_);
        v_k_6017_ = crate::leanh::lean_ctor_get(v_x_6011_, 1);
        crate::leanh::lean_inc(v_k_6017_);
        v_v_6018_ = crate::leanh::lean_ctor_get(v_x_6011_, 2);
        crate::leanh::lean_inc(v_v_6018_);
        v_l_6019_ = crate::leanh::lean_ctor_get(v_x_6011_, 3);
        crate::leanh::lean_inc(v_l_6019_);
        v_r_6020_ = crate::leanh::lean_ctor_get(v_x_6011_, 4);
        crate::leanh::lean_inc(v_r_6020_);
        crate::leanh::lean_dec_ref_known(v_x_6011_, 5);
        v___x_6021_ = crate::leanh::lean_apply_7(
            v_h__2_6015_,
            v_size_6016_,
            v_k_6017_,
            v_v_6018_,
            v_l_6019_,
            v_r_6020_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6021_;
    } else {
        let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6015_);
        v___x_6022_ = crate::leanh::lean_apply_2(
            v_h__1_6014_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6022_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(
    mut v_00_u03b1_6023_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6024_: *mut crate::leanh::LeanObject,
    mut v_inst_6025_: *mut crate::leanh::LeanObject,
    mut v_k_6026_: *mut crate::leanh::LeanObject,
    mut v_motive_6027_: *mut crate::leanh::LeanObject,
    mut v_x_6028_: *mut crate::leanh::LeanObject,
    mut v_x_6029_: *mut crate::leanh::LeanObject,
    mut v_x_6030_: *mut crate::leanh::LeanObject,
    mut v_h__1_6031_: *mut crate::leanh::LeanObject,
    mut v_h__2_6032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6033_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(v_00_u03b1_6023_, v_00_u03b2_6024_, v_inst_6025_, v_k_6026_, v_motive_6027_, v_x_6028_, v_x_6029_, v_x_6030_, v_h__1_6031_, v_h__2_6032_);
    crate::leanh::lean_dec(v_k_6026_);
    crate::leanh::lean_dec_ref(v_inst_6025_);
    return v_res_6033_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(
    mut v_x_6034_: *mut crate::leanh::LeanObject,
    mut v_x_6035_: *mut crate::leanh::LeanObject,
    mut v_h__1_6036_: *mut crate::leanh::LeanObject,
    mut v_h__2_6037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6034_) == 0 {
        let mut v_size_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6036_);
        v_size_6038_ = crate::leanh::lean_ctor_get(v_x_6034_, 0);
        crate::leanh::lean_inc(v_size_6038_);
        v_k_6039_ = crate::leanh::lean_ctor_get(v_x_6034_, 1);
        crate::leanh::lean_inc(v_k_6039_);
        v_v_6040_ = crate::leanh::lean_ctor_get(v_x_6034_, 2);
        crate::leanh::lean_inc(v_v_6040_);
        v_l_6041_ = crate::leanh::lean_ctor_get(v_x_6034_, 3);
        crate::leanh::lean_inc(v_l_6041_);
        v_r_6042_ = crate::leanh::lean_ctor_get(v_x_6034_, 4);
        crate::leanh::lean_inc(v_r_6042_);
        crate::leanh::lean_dec_ref_known(v_x_6034_, 5);
        v___x_6043_ = crate::leanh::lean_apply_6(
            v_h__2_6037_,
            v_size_6038_,
            v_k_6039_,
            v_v_6040_,
            v_l_6041_,
            v_r_6042_,
            v_x_6035_,
        );
        return v___x_6043_;
    } else {
        let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6037_);
        v___x_6044_ = crate::leanh::lean_apply_1(v_h__1_6036_, v_x_6035_);
        return v___x_6044_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(
    mut v_00_u03b1_6045_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6046_: *mut crate::leanh::LeanObject,
    mut v_motive_6047_: *mut crate::leanh::LeanObject,
    mut v_x_6048_: *mut crate::leanh::LeanObject,
    mut v_x_6049_: *mut crate::leanh::LeanObject,
    mut v_h__1_6050_: *mut crate::leanh::LeanObject,
    mut v_h__2_6051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6048_) == 0 {
        let mut v_size_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6050_);
        v_size_6052_ = crate::leanh::lean_ctor_get(v_x_6048_, 0);
        crate::leanh::lean_inc(v_size_6052_);
        v_k_6053_ = crate::leanh::lean_ctor_get(v_x_6048_, 1);
        crate::leanh::lean_inc(v_k_6053_);
        v_v_6054_ = crate::leanh::lean_ctor_get(v_x_6048_, 2);
        crate::leanh::lean_inc(v_v_6054_);
        v_l_6055_ = crate::leanh::lean_ctor_get(v_x_6048_, 3);
        crate::leanh::lean_inc(v_l_6055_);
        v_r_6056_ = crate::leanh::lean_ctor_get(v_x_6048_, 4);
        crate::leanh::lean_inc(v_r_6056_);
        crate::leanh::lean_dec_ref_known(v_x_6048_, 5);
        v___x_6057_ = crate::leanh::lean_apply_6(
            v_h__2_6051_,
            v_size_6052_,
            v_k_6053_,
            v_v_6054_,
            v_l_6055_,
            v_r_6056_,
            v_x_6049_,
        );
        return v___x_6057_;
    } else {
        let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6051_);
        v___x_6058_ = crate::leanh::lean_apply_1(v_h__1_6050_, v_x_6049_);
        return v___x_6058_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(
    mut v_x_6059_: *mut crate::leanh::LeanObject,
    mut v_x_6060_: *mut crate::leanh::LeanObject,
    mut v_h__1_6061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_6062_ = crate::leanh::lean_ctor_get(v_x_6059_, 0);
    crate::leanh::lean_inc(v_size_6062_);
    v_k_6063_ = crate::leanh::lean_ctor_get(v_x_6059_, 1);
    crate::leanh::lean_inc(v_k_6063_);
    v_v_6064_ = crate::leanh::lean_ctor_get(v_x_6059_, 2);
    crate::leanh::lean_inc(v_v_6064_);
    v_l_6065_ = crate::leanh::lean_ctor_get(v_x_6059_, 3);
    crate::leanh::lean_inc(v_l_6065_);
    v_r_6066_ = crate::leanh::lean_ctor_get(v_x_6059_, 4);
    crate::leanh::lean_inc(v_r_6066_);
    crate::leanh::lean_dec(v_x_6059_);
    v___x_6067_ = crate::leanh::lean_apply_8(
        v_h__1_6061_,
        v_size_6062_,
        v_k_6063_,
        v_v_6064_,
        v_l_6065_,
        v_r_6066_,
        crate::leanh::lean_box(0),
        v_x_6060_,
        crate::leanh::lean_box(0),
    );
    return v___x_6067_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(
    mut v_00_u03b1_6068_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6069_: *mut crate::leanh::LeanObject,
    mut v_motive_6070_: *mut crate::leanh::LeanObject,
    mut v_x_6071_: *mut crate::leanh::LeanObject,
    mut v_x_6072_: *mut crate::leanh::LeanObject,
    mut v_x_6073_: *mut crate::leanh::LeanObject,
    mut v_x_6074_: *mut crate::leanh::LeanObject,
    mut v_h__1_6075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_6076_ = crate::leanh::lean_ctor_get(v_x_6071_, 0);
    crate::leanh::lean_inc(v_size_6076_);
    v_k_6077_ = crate::leanh::lean_ctor_get(v_x_6071_, 1);
    crate::leanh::lean_inc(v_k_6077_);
    v_v_6078_ = crate::leanh::lean_ctor_get(v_x_6071_, 2);
    crate::leanh::lean_inc(v_v_6078_);
    v_l_6079_ = crate::leanh::lean_ctor_get(v_x_6071_, 3);
    crate::leanh::lean_inc(v_l_6079_);
    v_r_6080_ = crate::leanh::lean_ctor_get(v_x_6071_, 4);
    crate::leanh::lean_inc(v_r_6080_);
    crate::leanh::lean_dec(v_x_6071_);
    v___x_6081_ = crate::leanh::lean_apply_8(
        v_h__1_6075_,
        v_size_6076_,
        v_k_6077_,
        v_v_6078_,
        v_l_6079_,
        v_r_6080_,
        crate::leanh::lean_box(0),
        v_x_6073_,
        crate::leanh::lean_box(0),
    );
    return v___x_6081_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(
    mut v_x_6082_: *mut crate::leanh::LeanObject,
    mut v_x_6083_: *mut crate::leanh::LeanObject,
    mut v_x_6084_: *mut crate::leanh::LeanObject,
    mut v_h__1_6085_: *mut crate::leanh::LeanObject,
    mut v_h__2_6086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6082_) == 0 {
        let mut v_size_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6085_);
        v_size_6087_ = crate::leanh::lean_ctor_get(v_x_6082_, 0);
        crate::leanh::lean_inc(v_size_6087_);
        v_k_6088_ = crate::leanh::lean_ctor_get(v_x_6082_, 1);
        crate::leanh::lean_inc(v_k_6088_);
        v_v_6089_ = crate::leanh::lean_ctor_get(v_x_6082_, 2);
        crate::leanh::lean_inc(v_v_6089_);
        v_l_6090_ = crate::leanh::lean_ctor_get(v_x_6082_, 3);
        crate::leanh::lean_inc(v_l_6090_);
        v_r_6091_ = crate::leanh::lean_ctor_get(v_x_6082_, 4);
        crate::leanh::lean_inc(v_r_6091_);
        crate::leanh::lean_dec_ref_known(v_x_6082_, 5);
        v___x_6092_ = crate::leanh::lean_apply_7(
            v_h__2_6086_,
            v_size_6087_,
            v_k_6088_,
            v_v_6089_,
            v_l_6090_,
            v_r_6091_,
            v_x_6083_,
            v_x_6084_,
        );
        return v___x_6092_;
    } else {
        let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6086_);
        v___x_6093_ = crate::leanh::lean_apply_2(v_h__1_6085_, v_x_6083_, v_x_6084_);
        return v___x_6093_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(
    mut v_00_u03b1_6094_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6095_: *mut crate::leanh::LeanObject,
    mut v_motive_6096_: *mut crate::leanh::LeanObject,
    mut v_x_6097_: *mut crate::leanh::LeanObject,
    mut v_x_6098_: *mut crate::leanh::LeanObject,
    mut v_x_6099_: *mut crate::leanh::LeanObject,
    mut v_h__1_6100_: *mut crate::leanh::LeanObject,
    mut v_h__2_6101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6097_) == 0 {
        let mut v_size_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6100_);
        v_size_6102_ = crate::leanh::lean_ctor_get(v_x_6097_, 0);
        crate::leanh::lean_inc(v_size_6102_);
        v_k_6103_ = crate::leanh::lean_ctor_get(v_x_6097_, 1);
        crate::leanh::lean_inc(v_k_6103_);
        v_v_6104_ = crate::leanh::lean_ctor_get(v_x_6097_, 2);
        crate::leanh::lean_inc(v_v_6104_);
        v_l_6105_ = crate::leanh::lean_ctor_get(v_x_6097_, 3);
        crate::leanh::lean_inc(v_l_6105_);
        v_r_6106_ = crate::leanh::lean_ctor_get(v_x_6097_, 4);
        crate::leanh::lean_inc(v_r_6106_);
        crate::leanh::lean_dec_ref_known(v_x_6097_, 5);
        v___x_6107_ = crate::leanh::lean_apply_7(
            v_h__2_6101_,
            v_size_6102_,
            v_k_6103_,
            v_v_6104_,
            v_l_6105_,
            v_r_6106_,
            v_x_6098_,
            v_x_6099_,
        );
        return v___x_6107_;
    } else {
        let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6101_);
        v___x_6108_ = crate::leanh::lean_apply_2(v_h__1_6100_, v_x_6098_, v_x_6099_);
        return v___x_6108_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(
    mut v_x_6109_: *mut crate::leanh::LeanObject,
    mut v_h__1_6110_: *mut crate::leanh::LeanObject,
    mut v_h__2_6111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6109_) == 0 {
        let mut v_size_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6110_);
        v_size_6112_ = crate::leanh::lean_ctor_get(v_x_6109_, 0);
        crate::leanh::lean_inc(v_size_6112_);
        v_k_6113_ = crate::leanh::lean_ctor_get(v_x_6109_, 1);
        crate::leanh::lean_inc(v_k_6113_);
        v_v_6114_ = crate::leanh::lean_ctor_get(v_x_6109_, 2);
        crate::leanh::lean_inc(v_v_6114_);
        v_l_6115_ = crate::leanh::lean_ctor_get(v_x_6109_, 3);
        crate::leanh::lean_inc(v_l_6115_);
        v_r_6116_ = crate::leanh::lean_ctor_get(v_x_6109_, 4);
        crate::leanh::lean_inc(v_r_6116_);
        crate::leanh::lean_dec_ref_known(v_x_6109_, 5);
        v___x_6117_ = crate::leanh::lean_apply_7(
            v_h__2_6111_,
            v_size_6112_,
            v_k_6113_,
            v_v_6114_,
            v_l_6115_,
            v_r_6116_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6117_;
    } else {
        let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6111_);
        v___x_6118_ = crate::leanh::lean_apply_2(
            v_h__1_6110_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6118_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(
    mut v_00_u03b1_6119_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6120_: *mut crate::leanh::LeanObject,
    mut v_inst_6121_: *mut crate::leanh::LeanObject,
    mut v_k_6122_: *mut crate::leanh::LeanObject,
    mut v_motive_6123_: *mut crate::leanh::LeanObject,
    mut v_x_6124_: *mut crate::leanh::LeanObject,
    mut v_x_6125_: *mut crate::leanh::LeanObject,
    mut v_x_6126_: *mut crate::leanh::LeanObject,
    mut v_h__1_6127_: *mut crate::leanh::LeanObject,
    mut v_h__2_6128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6124_) == 0 {
        let mut v_size_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6127_);
        v_size_6129_ = crate::leanh::lean_ctor_get(v_x_6124_, 0);
        crate::leanh::lean_inc(v_size_6129_);
        v_k_6130_ = crate::leanh::lean_ctor_get(v_x_6124_, 1);
        crate::leanh::lean_inc(v_k_6130_);
        v_v_6131_ = crate::leanh::lean_ctor_get(v_x_6124_, 2);
        crate::leanh::lean_inc(v_v_6131_);
        v_l_6132_ = crate::leanh::lean_ctor_get(v_x_6124_, 3);
        crate::leanh::lean_inc(v_l_6132_);
        v_r_6133_ = crate::leanh::lean_ctor_get(v_x_6124_, 4);
        crate::leanh::lean_inc(v_r_6133_);
        crate::leanh::lean_dec_ref_known(v_x_6124_, 5);
        v___x_6134_ = crate::leanh::lean_apply_7(
            v_h__2_6128_,
            v_size_6129_,
            v_k_6130_,
            v_v_6131_,
            v_l_6132_,
            v_r_6133_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6134_;
    } else {
        let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6128_);
        v___x_6135_ = crate::leanh::lean_apply_2(
            v_h__1_6127_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6135_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(
    mut v_00_u03b1_6136_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6137_: *mut crate::leanh::LeanObject,
    mut v_inst_6138_: *mut crate::leanh::LeanObject,
    mut v_k_6139_: *mut crate::leanh::LeanObject,
    mut v_motive_6140_: *mut crate::leanh::LeanObject,
    mut v_x_6141_: *mut crate::leanh::LeanObject,
    mut v_x_6142_: *mut crate::leanh::LeanObject,
    mut v_x_6143_: *mut crate::leanh::LeanObject,
    mut v_h__1_6144_: *mut crate::leanh::LeanObject,
    mut v_h__2_6145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6146_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(v_00_u03b1_6136_, v_00_u03b2_6137_, v_inst_6138_, v_k_6139_, v_motive_6140_, v_x_6141_, v_x_6142_, v_x_6143_, v_h__1_6144_, v_h__2_6145_);
    crate::leanh::lean_dec(v_k_6139_);
    crate::leanh::lean_dec_ref(v_inst_6138_);
    return v_res_6146_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(
    mut v_x_6147_: *mut crate::leanh::LeanObject,
    mut v_h__1_6148_: *mut crate::leanh::LeanObject,
    mut v_h__2_6149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6147_) == 0 {
        let mut v_size_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6148_);
        v_size_6150_ = crate::leanh::lean_ctor_get(v_x_6147_, 0);
        crate::leanh::lean_inc(v_size_6150_);
        v_k_6151_ = crate::leanh::lean_ctor_get(v_x_6147_, 1);
        crate::leanh::lean_inc(v_k_6151_);
        v_v_6152_ = crate::leanh::lean_ctor_get(v_x_6147_, 2);
        crate::leanh::lean_inc(v_v_6152_);
        v_l_6153_ = crate::leanh::lean_ctor_get(v_x_6147_, 3);
        crate::leanh::lean_inc(v_l_6153_);
        v_r_6154_ = crate::leanh::lean_ctor_get(v_x_6147_, 4);
        crate::leanh::lean_inc(v_r_6154_);
        crate::leanh::lean_dec_ref_known(v_x_6147_, 5);
        v___x_6155_ = crate::leanh::lean_apply_7(
            v_h__2_6149_,
            v_size_6150_,
            v_k_6151_,
            v_v_6152_,
            v_l_6153_,
            v_r_6154_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6155_;
    } else {
        let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6149_);
        v___x_6156_ = crate::leanh::lean_apply_2(
            v_h__1_6148_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6156_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(
    mut v_00_u03b1_6157_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6158_: *mut crate::leanh::LeanObject,
    mut v_inst_6159_: *mut crate::leanh::LeanObject,
    mut v_k_6160_: *mut crate::leanh::LeanObject,
    mut v_motive_6161_: *mut crate::leanh::LeanObject,
    mut v_x_6162_: *mut crate::leanh::LeanObject,
    mut v_x_6163_: *mut crate::leanh::LeanObject,
    mut v_x_6164_: *mut crate::leanh::LeanObject,
    mut v_h__1_6165_: *mut crate::leanh::LeanObject,
    mut v_h__2_6166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6162_) == 0 {
        let mut v_size_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6165_);
        v_size_6167_ = crate::leanh::lean_ctor_get(v_x_6162_, 0);
        crate::leanh::lean_inc(v_size_6167_);
        v_k_6168_ = crate::leanh::lean_ctor_get(v_x_6162_, 1);
        crate::leanh::lean_inc(v_k_6168_);
        v_v_6169_ = crate::leanh::lean_ctor_get(v_x_6162_, 2);
        crate::leanh::lean_inc(v_v_6169_);
        v_l_6170_ = crate::leanh::lean_ctor_get(v_x_6162_, 3);
        crate::leanh::lean_inc(v_l_6170_);
        v_r_6171_ = crate::leanh::lean_ctor_get(v_x_6162_, 4);
        crate::leanh::lean_inc(v_r_6171_);
        crate::leanh::lean_dec_ref_known(v_x_6162_, 5);
        v___x_6172_ = crate::leanh::lean_apply_7(
            v_h__2_6166_,
            v_size_6167_,
            v_k_6168_,
            v_v_6169_,
            v_l_6170_,
            v_r_6171_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6172_;
    } else {
        let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6166_);
        v___x_6173_ = crate::leanh::lean_apply_2(
            v_h__1_6165_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6173_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(
    mut v_00_u03b1_6174_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6175_: *mut crate::leanh::LeanObject,
    mut v_inst_6176_: *mut crate::leanh::LeanObject,
    mut v_k_6177_: *mut crate::leanh::LeanObject,
    mut v_motive_6178_: *mut crate::leanh::LeanObject,
    mut v_x_6179_: *mut crate::leanh::LeanObject,
    mut v_x_6180_: *mut crate::leanh::LeanObject,
    mut v_x_6181_: *mut crate::leanh::LeanObject,
    mut v_h__1_6182_: *mut crate::leanh::LeanObject,
    mut v_h__2_6183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6184_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(v_00_u03b1_6174_, v_00_u03b2_6175_, v_inst_6176_, v_k_6177_, v_motive_6178_, v_x_6179_, v_x_6180_, v_x_6181_, v_h__1_6182_, v_h__2_6183_);
    crate::leanh::lean_dec(v_k_6177_);
    crate::leanh::lean_dec_ref(v_inst_6176_);
    return v_res_6184_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(
    mut v_x_6185_: *mut crate::leanh::LeanObject,
    mut v_h__1_6186_: *mut crate::leanh::LeanObject,
    mut v_h__2_6187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6185_) == 0 {
        let mut v_size_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6186_);
        v_size_6188_ = crate::leanh::lean_ctor_get(v_x_6185_, 0);
        crate::leanh::lean_inc(v_size_6188_);
        v_k_6189_ = crate::leanh::lean_ctor_get(v_x_6185_, 1);
        crate::leanh::lean_inc(v_k_6189_);
        v_v_6190_ = crate::leanh::lean_ctor_get(v_x_6185_, 2);
        crate::leanh::lean_inc(v_v_6190_);
        v_l_6191_ = crate::leanh::lean_ctor_get(v_x_6185_, 3);
        crate::leanh::lean_inc(v_l_6191_);
        v_r_6192_ = crate::leanh::lean_ctor_get(v_x_6185_, 4);
        crate::leanh::lean_inc(v_r_6192_);
        crate::leanh::lean_dec_ref_known(v_x_6185_, 5);
        v___x_6193_ = crate::leanh::lean_apply_7(
            v_h__2_6187_,
            v_size_6188_,
            v_k_6189_,
            v_v_6190_,
            v_l_6191_,
            v_r_6192_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6193_;
    } else {
        let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6187_);
        v___x_6194_ = crate::leanh::lean_apply_2(
            v_h__1_6186_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6194_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(
    mut v_00_u03b1_6195_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6196_: *mut crate::leanh::LeanObject,
    mut v_inst_6197_: *mut crate::leanh::LeanObject,
    mut v_k_6198_: *mut crate::leanh::LeanObject,
    mut v_motive_6199_: *mut crate::leanh::LeanObject,
    mut v_x_6200_: *mut crate::leanh::LeanObject,
    mut v_x_6201_: *mut crate::leanh::LeanObject,
    mut v_x_6202_: *mut crate::leanh::LeanObject,
    mut v_h__1_6203_: *mut crate::leanh::LeanObject,
    mut v_h__2_6204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6200_) == 0 {
        let mut v_size_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6203_);
        v_size_6205_ = crate::leanh::lean_ctor_get(v_x_6200_, 0);
        crate::leanh::lean_inc(v_size_6205_);
        v_k_6206_ = crate::leanh::lean_ctor_get(v_x_6200_, 1);
        crate::leanh::lean_inc(v_k_6206_);
        v_v_6207_ = crate::leanh::lean_ctor_get(v_x_6200_, 2);
        crate::leanh::lean_inc(v_v_6207_);
        v_l_6208_ = crate::leanh::lean_ctor_get(v_x_6200_, 3);
        crate::leanh::lean_inc(v_l_6208_);
        v_r_6209_ = crate::leanh::lean_ctor_get(v_x_6200_, 4);
        crate::leanh::lean_inc(v_r_6209_);
        crate::leanh::lean_dec_ref_known(v_x_6200_, 5);
        v___x_6210_ = crate::leanh::lean_apply_7(
            v_h__2_6204_,
            v_size_6205_,
            v_k_6206_,
            v_v_6207_,
            v_l_6208_,
            v_r_6209_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6210_;
    } else {
        let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6204_);
        v___x_6211_ = crate::leanh::lean_apply_2(
            v_h__1_6203_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6211_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(
    mut v_00_u03b1_6212_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6213_: *mut crate::leanh::LeanObject,
    mut v_inst_6214_: *mut crate::leanh::LeanObject,
    mut v_k_6215_: *mut crate::leanh::LeanObject,
    mut v_motive_6216_: *mut crate::leanh::LeanObject,
    mut v_x_6217_: *mut crate::leanh::LeanObject,
    mut v_x_6218_: *mut crate::leanh::LeanObject,
    mut v_x_6219_: *mut crate::leanh::LeanObject,
    mut v_h__1_6220_: *mut crate::leanh::LeanObject,
    mut v_h__2_6221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6222_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(v_00_u03b1_6212_, v_00_u03b2_6213_, v_inst_6214_, v_k_6215_, v_motive_6216_, v_x_6217_, v_x_6218_, v_x_6219_, v_h__1_6220_, v_h__2_6221_);
    crate::leanh::lean_dec(v_k_6215_);
    crate::leanh::lean_dec_ref(v_inst_6214_);
    return v_res_6222_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(
    mut v_x_6223_: *mut crate::leanh::LeanObject,
    mut v_h__1_6224_: *mut crate::leanh::LeanObject,
    mut v_h__2_6225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6223_) == 0 {
        let mut v_size_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6224_);
        v_size_6226_ = crate::leanh::lean_ctor_get(v_x_6223_, 0);
        crate::leanh::lean_inc(v_size_6226_);
        v_k_6227_ = crate::leanh::lean_ctor_get(v_x_6223_, 1);
        crate::leanh::lean_inc(v_k_6227_);
        v_v_6228_ = crate::leanh::lean_ctor_get(v_x_6223_, 2);
        crate::leanh::lean_inc(v_v_6228_);
        v_l_6229_ = crate::leanh::lean_ctor_get(v_x_6223_, 3);
        crate::leanh::lean_inc(v_l_6229_);
        v_r_6230_ = crate::leanh::lean_ctor_get(v_x_6223_, 4);
        crate::leanh::lean_inc(v_r_6230_);
        crate::leanh::lean_dec_ref_known(v_x_6223_, 5);
        v___x_6231_ = crate::leanh::lean_apply_7(
            v_h__2_6225_,
            v_size_6226_,
            v_k_6227_,
            v_v_6228_,
            v_l_6229_,
            v_r_6230_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6231_;
    } else {
        let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6225_);
        v___x_6232_ = crate::leanh::lean_apply_2(
            v_h__1_6224_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6232_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(
    mut v_00_u03b1_6233_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6234_: *mut crate::leanh::LeanObject,
    mut v_inst_6235_: *mut crate::leanh::LeanObject,
    mut v_k_6236_: *mut crate::leanh::LeanObject,
    mut v_motive_6237_: *mut crate::leanh::LeanObject,
    mut v_x_6238_: *mut crate::leanh::LeanObject,
    mut v_x_6239_: *mut crate::leanh::LeanObject,
    mut v_x_6240_: *mut crate::leanh::LeanObject,
    mut v_h__1_6241_: *mut crate::leanh::LeanObject,
    mut v_h__2_6242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6238_) == 0 {
        let mut v_size_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6241_);
        v_size_6243_ = crate::leanh::lean_ctor_get(v_x_6238_, 0);
        crate::leanh::lean_inc(v_size_6243_);
        v_k_6244_ = crate::leanh::lean_ctor_get(v_x_6238_, 1);
        crate::leanh::lean_inc(v_k_6244_);
        v_v_6245_ = crate::leanh::lean_ctor_get(v_x_6238_, 2);
        crate::leanh::lean_inc(v_v_6245_);
        v_l_6246_ = crate::leanh::lean_ctor_get(v_x_6238_, 3);
        crate::leanh::lean_inc(v_l_6246_);
        v_r_6247_ = crate::leanh::lean_ctor_get(v_x_6238_, 4);
        crate::leanh::lean_inc(v_r_6247_);
        crate::leanh::lean_dec_ref_known(v_x_6238_, 5);
        v___x_6248_ = crate::leanh::lean_apply_7(
            v_h__2_6242_,
            v_size_6243_,
            v_k_6244_,
            v_v_6245_,
            v_l_6246_,
            v_r_6247_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6248_;
    } else {
        let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6242_);
        v___x_6249_ = crate::leanh::lean_apply_2(
            v_h__1_6241_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_6249_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(
    mut v_00_u03b1_6250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6251_: *mut crate::leanh::LeanObject,
    mut v_inst_6252_: *mut crate::leanh::LeanObject,
    mut v_k_6253_: *mut crate::leanh::LeanObject,
    mut v_motive_6254_: *mut crate::leanh::LeanObject,
    mut v_x_6255_: *mut crate::leanh::LeanObject,
    mut v_x_6256_: *mut crate::leanh::LeanObject,
    mut v_x_6257_: *mut crate::leanh::LeanObject,
    mut v_h__1_6258_: *mut crate::leanh::LeanObject,
    mut v_h__2_6259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6260_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(v_00_u03b1_6250_, v_00_u03b2_6251_, v_inst_6252_, v_k_6253_, v_motive_6254_, v_x_6255_, v_x_6256_, v_x_6257_, v_h__1_6258_, v_h__2_6259_);
    crate::leanh::lean_dec(v_k_6253_);
    crate::leanh::lean_dec_ref(v_inst_6252_);
    return v_res_6260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_Model(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_Model(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_Model(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_Model(builtin);
}
