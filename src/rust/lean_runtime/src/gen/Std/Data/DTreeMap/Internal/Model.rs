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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_apply_6, lean_apply_7,
    lean_apply_8, lean_apply_9, lean_apply_10, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0_value: LeanStringObject<
    26,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1_value: LeanStringObject<
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
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2_value: LeanStringObject<
    14,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0_value
)
    as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0_value
) as *mut LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(
    mut v_k_3131_: *mut LeanObject,
    mut v_l_3132_: *mut LeanObject,
) -> u8 {
    let mut v_k_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_l_3132_) == 0 {
                    v_k_3133_ = lean_ctor_get(v_l_3132_, 1);
                    lean_inc(v_k_3133_);
                    v_l_3134_ = lean_ctor_get(v_l_3132_, 3);
                    lean_inc(v_l_3134_);
                    v_r_3135_ = lean_ctor_get(v_l_3132_, 4);
                    lean_inc(v_r_3135_);
                    lean_dec_ref_known(v_l_3132_, 5);
                    lean_inc_ref(v_k_3131_);
                    v___x_3136_ = lean_apply_1(v_k_3131_, v_k_3133_);
                    v___x_3137_ = (lean_unbox(v___x_3136_) as u8);
                    match v___x_3137_ {
                        0 => {
                            lean_dec(v_r_3135_);
                            v_l_3132_ = v_l_3134_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_3135_);
                            lean_dec(v_l_3134_);
                            lean_dec_ref(v_k_3131_);
                            v___x_3139_ = 1;
                            return v___x_3139_;
                        }
                        _ => {
                            lean_dec(v_l_3134_);
                            v_l_3132_ = v_r_3135_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_k_3131_);
                    v___x_3141_ = 0;
                    return v___x_3141_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_x27___redArg___boxed(
    mut v_k_3142_: *mut LeanObject,
    mut v_l_3143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3144_: u8 = 0;
    let mut v_r_3145_: *mut LeanObject = core::ptr::null_mut();
    v_res_3144_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_3142_, v_l_3143_);
    v_r_3145_ = lean_box((v_res_3144_) as usize);
    return v_r_3145_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_x27(
    mut v_00_u03b1_3146_: *mut LeanObject,
    mut v_00_u03b2_3147_: *mut LeanObject,
    mut v_inst_3148_: *mut LeanObject,
    mut v_k_3149_: *mut LeanObject,
    mut v_l_3150_: *mut LeanObject,
) -> u8 {
    let mut v___x_3151_: u8 = 0;
    v___x_3151_ = l_Std_DTreeMap_Internal_Impl_contains_x27___redArg(v_k_3149_, v_l_3150_);
    return v___x_3151_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_x27___boxed(
    mut v_00_u03b1_3152_: *mut LeanObject,
    mut v_00_u03b2_3153_: *mut LeanObject,
    mut v_inst_3154_: *mut LeanObject,
    mut v_k_3155_: *mut LeanObject,
    mut v_l_3156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3157_: u8 = 0;
    let mut v_r_3158_: *mut LeanObject = core::ptr::null_mut();
    v_res_3157_ = l_Std_DTreeMap_Internal_Impl_contains_x27(
        v_00_u03b1_3152_,
        v_00_u03b2_3153_,
        v_inst_3154_,
        v_k_3155_,
        v_l_3156_,
    );
    lean_dec_ref(v_inst_3154_);
    v_r_3158_ = lean_box((v_res_3157_) as usize);
    return v_r_3158_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter___redArg(
    mut v_l_3159_: *mut LeanObject,
    mut v_h__1_3160_: *mut LeanObject,
    mut v_h__2_3161_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_3159_) == 0 {
        let mut v_size_3162_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3163_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_3164_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_3165_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_3166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_3160_);
        v_size_3162_ = lean_ctor_get(v_l_3159_, 0);
        lean_inc(v_size_3162_);
        v_k_3163_ = lean_ctor_get(v_l_3159_, 1);
        lean_inc(v_k_3163_);
        v_v_3164_ = lean_ctor_get(v_l_3159_, 2);
        lean_inc(v_v_3164_);
        v_l_3165_ = lean_ctor_get(v_l_3159_, 3);
        lean_inc(v_l_3165_);
        v_r_3166_ = lean_ctor_get(v_l_3159_, 4);
        lean_inc(v_r_3166_);
        lean_dec_ref_known(v_l_3159_, 5);
        v___x_3167_ = lean_apply_5(
            v_h__2_3161_,
            v_size_3162_,
            v_k_3163_,
            v_v_3164_,
            v_l_3165_,
            v_r_3166_,
        );
        return v___x_3167_;
    } else {
        let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_3161_);
        v___x_3168_ = lean_box(0);
        v___x_3169_ = lean_apply_1(v_h__1_3160_, v___x_3168_);
        return v___x_3169_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__3_splitter(
    mut v_00_u03b1_3170_: *mut LeanObject,
    mut v_00_u03b2_3171_: *mut LeanObject,
    mut v_motive_3172_: *mut LeanObject,
    mut v_l_3173_: *mut LeanObject,
    mut v_h__1_3174_: *mut LeanObject,
    mut v_h__2_3175_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_3173_) == 0 {
        let mut v_size_3176_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3177_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_3178_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_3179_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_3180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_3174_);
        v_size_3176_ = lean_ctor_get(v_l_3173_, 0);
        lean_inc(v_size_3176_);
        v_k_3177_ = lean_ctor_get(v_l_3173_, 1);
        lean_inc(v_k_3177_);
        v_v_3178_ = lean_ctor_get(v_l_3173_, 2);
        lean_inc(v_v_3178_);
        v_l_3179_ = lean_ctor_get(v_l_3173_, 3);
        lean_inc(v_l_3179_);
        v_r_3180_ = lean_ctor_get(v_l_3173_, 4);
        lean_inc(v_r_3180_);
        lean_dec_ref_known(v_l_3173_, 5);
        v___x_3181_ = lean_apply_5(
            v_h__2_3175_,
            v_size_3176_,
            v_k_3177_,
            v_v_3178_,
            v_l_3179_,
            v_r_3180_,
        );
        return v___x_3181_;
    } else {
        let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_3175_);
        v___x_3182_ = lean_box(0);
        v___x_3183_ = lean_apply_1(v_h__1_3174_, v___x_3182_);
        return v___x_3183_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(
    mut v_x_3184_: u8,
    mut v_h__1_3185_: *mut LeanObject,
    mut v_h__2_3186_: *mut LeanObject,
    mut v_h__3_3187_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_3184_ {
        0 => {
            let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3187_);
            lean_dec(v_h__2_3186_);
            v___x_3188_ = lean_box(0);
            v___x_3189_ = lean_apply_1(v_h__1_3185_, v___x_3188_);
            return v___x_3189_;
        }
        1 => {
            let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_3186_);
            lean_dec(v_h__1_3185_);
            v___x_3190_ = lean_box(0);
            v___x_3191_ = lean_apply_1(v_h__3_3187_, v___x_3190_);
            return v___x_3191_;
        }
        _ => {
            let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3187_);
            lean_dec(v_h__1_3185_);
            v___x_3192_ = lean_box(0);
            v___x_3193_ = lean_apply_1(v_h__2_3186_, v___x_3192_);
            return v___x_3193_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg___boxed(
    mut v_x_3194_: *mut LeanObject,
    mut v_h__1_3195_: *mut LeanObject,
    mut v_h__2_3196_: *mut LeanObject,
    mut v_h__3_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_3198_: u8 = 0;
    let mut v_res_3199_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_3198_ = (lean_unbox(v_x_3194_) as u8);
    v_res_3199_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___redArg(v_x_36__boxed_3198_, v_h__1_3195_, v_h__2_3196_, v_h__3_3197_);
    return v_res_3199_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(
    mut v_motive_3200_: *mut LeanObject,
    mut v_x_3201_: u8,
    mut v_h__1_3202_: *mut LeanObject,
    mut v_h__2_3203_: *mut LeanObject,
    mut v_h__3_3204_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_3201_ {
        0 => {
            let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3204_);
            lean_dec(v_h__2_3203_);
            v___x_3205_ = lean_box(0);
            v___x_3206_ = lean_apply_1(v_h__1_3202_, v___x_3205_);
            return v___x_3206_;
        }
        1 => {
            let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_3203_);
            lean_dec(v_h__1_3202_);
            v___x_3207_ = lean_box(0);
            v___x_3208_ = lean_apply_1(v_h__3_3204_, v___x_3207_);
            return v___x_3208_;
        }
        _ => {
            let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3204_);
            lean_dec(v_h__1_3202_);
            v___x_3209_ = lean_box(0);
            v___x_3210_ = lean_apply_1(v_h__2_3203_, v___x_3209_);
            return v___x_3210_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter___boxed(
    mut v_motive_3211_: *mut LeanObject,
    mut v_x_3212_: *mut LeanObject,
    mut v_h__1_3213_: *mut LeanObject,
    mut v_h__2_3214_: *mut LeanObject,
    mut v_h__3_3215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_3216_: u8 = 0;
    let mut v_res_3217_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_3216_ = (lean_unbox(v_x_3212_) as u8);
    v_res_3217_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_x27_match__1_splitter(v_motive_3211_, v_x_51__boxed_3216_, v_h__1_3213_, v_h__2_3214_, v_h__3_3215_);
    return v_res_3217_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(
    mut v_x_3218_: u8,
    mut v_h__1_3219_: *mut LeanObject,
    mut v_h__2_3220_: *mut LeanObject,
    mut v_h__3_3221_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_3218_ {
        0 => {
            let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3221_);
            lean_dec(v_h__2_3220_);
            v___x_3222_ = lean_box(0);
            v___x_3223_ = lean_apply_1(v_h__1_3219_, v___x_3222_);
            return v___x_3223_;
        }
        1 => {
            let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_3220_);
            lean_dec(v_h__1_3219_);
            v___x_3224_ = lean_box(0);
            v___x_3225_ = lean_apply_1(v_h__3_3221_, v___x_3224_);
            return v___x_3225_;
        }
        _ => {
            let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3221_);
            lean_dec(v_h__1_3219_);
            v___x_3226_ = lean_box(0);
            v___x_3227_ = lean_apply_1(v_h__2_3220_, v___x_3226_);
            return v___x_3227_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(
    mut v_x_3228_: *mut LeanObject,
    mut v_h__1_3229_: *mut LeanObject,
    mut v_h__2_3230_: *mut LeanObject,
    mut v_h__3_3231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_3232_: u8 = 0;
    let mut v_res_3233_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_3232_ = (lean_unbox(v_x_3228_) as u8);
    v_res_3233_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_36__boxed_3232_, v_h__1_3229_, v_h__2_3230_, v_h__3_3231_);
    return v_res_3233_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(
    mut v_motive_3234_: *mut LeanObject,
    mut v_x_3235_: u8,
    mut v_h__1_3236_: *mut LeanObject,
    mut v_h__2_3237_: *mut LeanObject,
    mut v_h__3_3238_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_3235_ {
        0 => {
            let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3238_);
            lean_dec(v_h__2_3237_);
            v___x_3239_ = lean_box(0);
            v___x_3240_ = lean_apply_1(v_h__1_3236_, v___x_3239_);
            return v___x_3240_;
        }
        1 => {
            let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_3237_);
            lean_dec(v_h__1_3236_);
            v___x_3241_ = lean_box(0);
            v___x_3242_ = lean_apply_1(v_h__3_3238_, v___x_3241_);
            return v___x_3242_;
        }
        _ => {
            let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3238_);
            lean_dec(v_h__1_3236_);
            v___x_3243_ = lean_box(0);
            v___x_3244_ = lean_apply_1(v_h__2_3237_, v___x_3243_);
            return v___x_3244_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(
    mut v_motive_3245_: *mut LeanObject,
    mut v_x_3246_: *mut LeanObject,
    mut v_h__1_3247_: *mut LeanObject,
    mut v_h__2_3248_: *mut LeanObject,
    mut v_h__3_3249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_3250_: u8 = 0;
    let mut v_res_3251_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_3250_ = (lean_unbox(v_x_3246_) as u8);
    v_res_3251_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_3245_, v_x_51__boxed_3250_, v_h__1_3247_, v_h__2_3248_, v_h__3_3249_);
    return v_res_3251_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(
    mut v_k_3252_: *mut LeanObject,
    mut v_f_3253_: *mut LeanObject,
    mut v_ll_3254_: *mut LeanObject,
    mut v_m_3255_: *mut LeanObject,
    mut v_rr_3256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_3255_) == 0 {
                    v_k_3257_ = lean_ctor_get(v_m_3255_, 1);
                    lean_inc_n(v_k_3257_, 2);
                    v_v_3258_ = lean_ctor_get(v_m_3255_, 2);
                    lean_inc(v_v_3258_);
                    v_l_3259_ = lean_ctor_get(v_m_3255_, 3);
                    lean_inc(v_l_3259_);
                    v_r_3260_ = lean_ctor_get(v_m_3255_, 4);
                    lean_inc(v_r_3260_);
                    lean_dec_ref_known(v_m_3255_, 5);
                    lean_inc_ref(v_k_3252_);
                    v___x_3261_ = lean_apply_1(v_k_3252_, v_k_3257_);
                    v___x_3262_ = (lean_unbox(v___x_3261_) as u8);
                    match v___x_3262_ {
                        0 => {
                            v___x_3263_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_3263_, 0, v_k_3257_);
                            lean_ctor_set(v___x_3263_, 1, v_v_3258_);
                            v___x_3264_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_3260_);
                            lean_dec(v_r_3260_);
                            v___x_3265_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3265_, 0, v___x_3263_);
                            lean_ctor_set(v___x_3265_, 1, v___x_3264_);
                            v___x_3266_ = l_List_appendTR___redArg(v___x_3265_, v_rr_3256_);
                            v_m_3255_ = v_l_3259_;
                            v_rr_3256_ = v___x_3266_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec_ref(v_k_3252_);
                            v___x_3268_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_3259_);
                            lean_dec(v_l_3259_);
                            v___x_3269_ = l_List_appendTR___redArg(v_ll_3254_, v___x_3268_);
                            v___x_3270_ =
                                l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_3257_, v_v_3258_);
                            v___x_3271_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_3260_);
                            lean_dec(v_r_3260_);
                            v___x_3272_ = l_List_appendTR___redArg(v___x_3271_, v_rr_3256_);
                            v___x_3273_ = lean_apply_4(
                                v_f_3253_,
                                v___x_3269_,
                                v___x_3270_,
                                lean_box(0),
                                v___x_3272_,
                            );
                            return v___x_3273_;
                        }
                        _ => {
                            v___x_3274_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_3259_);
                            lean_dec(v_l_3259_);
                            v___x_3275_ = l_List_appendTR___redArg(v_ll_3254_, v___x_3274_);
                            v___x_3276_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_3276_, 0, v_k_3257_);
                            lean_ctor_set(v___x_3276_, 1, v_v_3258_);
                            v___x_3277_ = lean_box(0);
                            v___x_3278_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3278_, 0, v___x_3276_);
                            lean_ctor_set(v___x_3278_, 1, v___x_3277_);
                            v___x_3279_ = l_List_appendTR___redArg(v___x_3275_, v___x_3278_);
                            v_ll_3254_ = v___x_3279_;
                            v_m_3255_ = v_r_3260_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_k_3252_);
                    v___x_3281_ = lean_box(0);
                    v___x_3282_ =
                        lean_apply_4(v_f_3253_, v_ll_3254_, v___x_3281_, lean_box(0), v_rr_3256_);
                    return v___x_3282_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition_go(
    mut v_00_u03b1_3283_: *mut LeanObject,
    mut v_00_u03b2_3284_: *mut LeanObject,
    mut v_00_u03b4_3285_: *mut LeanObject,
    mut v_inst_3286_: *mut LeanObject,
    mut v_k_3287_: *mut LeanObject,
    mut v_l_3288_: *mut LeanObject,
    mut v_f_3289_: *mut LeanObject,
    mut v_ll_3290_: *mut LeanObject,
    mut v_m_3291_: *mut LeanObject,
    mut v_hm_3292_: *mut LeanObject,
    mut v_rr_3293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    v___x_3294_ = l_Std_DTreeMap_Internal_Impl_applyPartition_go___redArg(
        v_k_3287_, v_f_3289_, v_ll_3290_, v_m_3291_, v_rr_3293_,
    );
    return v___x_3294_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition_go___boxed(
    mut v_00_u03b1_3295_: *mut LeanObject,
    mut v_00_u03b2_3296_: *mut LeanObject,
    mut v_00_u03b4_3297_: *mut LeanObject,
    mut v_inst_3298_: *mut LeanObject,
    mut v_k_3299_: *mut LeanObject,
    mut v_l_3300_: *mut LeanObject,
    mut v_f_3301_: *mut LeanObject,
    mut v_ll_3302_: *mut LeanObject,
    mut v_m_3303_: *mut LeanObject,
    mut v_hm_3304_: *mut LeanObject,
    mut v_rr_3305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3306_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_l_3300_);
    lean_dec_ref(v_inst_3298_);
    return v_res_3306_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(
    mut v_k_3307_: *mut LeanObject,
    mut v_l_3308_: *mut LeanObject,
    mut v_f_3309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    v___x_3310_ = lean_box(0);
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
    mut v_00_u03b1_3312_: *mut LeanObject,
    mut v_00_u03b2_3313_: *mut LeanObject,
    mut v_00_u03b4_3314_: *mut LeanObject,
    mut v_inst_3315_: *mut LeanObject,
    mut v_k_3316_: *mut LeanObject,
    mut v_l_3317_: *mut LeanObject,
    mut v_f_3318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    v___x_3319_ =
        l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v_k_3316_, v_l_3317_, v_f_3318_);
    return v___x_3319_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyPartition___boxed(
    mut v_00_u03b1_3320_: *mut LeanObject,
    mut v_00_u03b2_3321_: *mut LeanObject,
    mut v_00_u03b4_3322_: *mut LeanObject,
    mut v_inst_3323_: *mut LeanObject,
    mut v_k_3324_: *mut LeanObject,
    mut v_l_3325_: *mut LeanObject,
    mut v_f_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3327_: *mut LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_Std_DTreeMap_Internal_Impl_applyPartition(
        v_00_u03b1_3320_,
        v_00_u03b2_3321_,
        v_00_u03b4_3322_,
        v_inst_3323_,
        v_k_3324_,
        v_l_3325_,
        v_f_3326_,
    );
    lean_dec_ref(v_inst_3323_);
    return v_res_3327_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0(
    mut v_f_3328_: *mut LeanObject,
    mut v_c_3329_: *mut LeanObject,
    mut v_h_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    v___x_3331_ = lean_apply_2(v_f_3328_, v_c_3329_, lean_box(0));
    return v___x_3331_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
    mut v_inst_3332_: *mut LeanObject,
    mut v_k_3333_: *mut LeanObject,
    mut v_l_3334_: *mut LeanObject,
    mut v_f_3335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___f_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_l_3334_) == 0 {
                    v_k_3336_ = lean_ctor_get(v_l_3334_, 1);
                    lean_inc_n(v_k_3336_, 2);
                    v_v_3337_ = lean_ctor_get(v_l_3334_, 2);
                    lean_inc(v_v_3337_);
                    v_l_3338_ = lean_ctor_get(v_l_3334_, 3);
                    lean_inc(v_l_3338_);
                    v_r_3339_ = lean_ctor_get(v_l_3334_, 4);
                    lean_inc(v_r_3339_);
                    lean_dec_ref_known(v_l_3334_, 5);
                    lean_inc_ref(v_inst_3332_);
                    lean_inc(v_k_3333_);
                    v___x_3340_ = lean_apply_2(v_inst_3332_, v_k_3333_, v_k_3336_);
                    v___x_3341_ = (lean_unbox(v___x_3340_) as u8);
                    match v___x_3341_ {
                        0 => {
                            lean_dec(v_r_3339_);
                            lean_dec(v_v_3337_);
                            lean_dec(v_k_3336_);
                            v___f_3342_ = lean_alloc_closure(
                                l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0
                                    as *mut core::ffi::c_void,
                                3,
                                1,
                            );
                            lean_closure_set(v___f_3342_, 0, v_f_3335_);
                            v_l_3334_ = v_l_3338_;
                            v_f_3335_ = v___f_3342_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_3339_);
                            lean_dec(v_l_3338_);
                            lean_dec(v_k_3333_);
                            lean_dec_ref(v_inst_3332_);
                            v___x_3344_ =
                                l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_3336_, v_v_3337_);
                            v___x_3345_ = lean_apply_2(v_f_3335_, v___x_3344_, lean_box(0));
                            return v___x_3345_;
                        }
                        _ => {
                            lean_dec(v_l_3338_);
                            lean_dec(v_v_3337_);
                            lean_dec(v_k_3336_);
                            v___f_3346_ = lean_alloc_closure(
                                l_Std_DTreeMap_Internal_Impl_applyCell___redArg___lam__0
                                    as *mut core::ffi::c_void,
                                3,
                                1,
                            );
                            lean_closure_set(v___f_3346_, 0, v_f_3335_);
                            v_l_3334_ = v_r_3339_;
                            v_f_3335_ = v___f_3346_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_3333_);
                    lean_dec_ref(v_inst_3332_);
                    v___x_3348_ = lean_box(0);
                    v___x_3349_ = lean_apply_2(v_f_3335_, v___x_3348_, lean_box(0));
                    return v___x_3349_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_applyCell(
    mut v_00_u03b1_3350_: *mut LeanObject,
    mut v_00_u03b2_3351_: *mut LeanObject,
    mut v_00_u03b4_3352_: *mut LeanObject,
    mut v_inst_3353_: *mut LeanObject,
    mut v_k_3354_: *mut LeanObject,
    mut v_l_3355_: *mut LeanObject,
    mut v_f_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    v___x_3357_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
        v_inst_3353_,
        v_k_3354_,
        v_l_3355_,
        v_f_3356_,
    );
    return v___x_3357_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___redArg(
    mut v_l_3358_: *mut LeanObject,
    mut v_f_3359_: *mut LeanObject,
    mut v_h__1_3360_: *mut LeanObject,
    mut v_h__2_3361_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_3358_) == 0 {
        let mut v_size_3362_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3363_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_3364_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_3365_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_3366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_3360_);
        v_size_3362_ = lean_ctor_get(v_l_3358_, 0);
        lean_inc(v_size_3362_);
        v_k_3363_ = lean_ctor_get(v_l_3358_, 1);
        lean_inc(v_k_3363_);
        v_v_3364_ = lean_ctor_get(v_l_3358_, 2);
        lean_inc(v_v_3364_);
        v_l_3365_ = lean_ctor_get(v_l_3358_, 3);
        lean_inc(v_l_3365_);
        v_r_3366_ = lean_ctor_get(v_l_3358_, 4);
        lean_inc(v_r_3366_);
        lean_dec_ref_known(v_l_3358_, 5);
        v___x_3367_ = lean_apply_6(
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
        let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_3361_);
        v___x_3368_ = lean_apply_1(v_h__1_3360_, v_f_3359_);
        return v___x_3368_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(
    mut v_00_u03b1_3369_: *mut LeanObject,
    mut v_00_u03b2_3370_: *mut LeanObject,
    mut v_00_u03b4_3371_: *mut LeanObject,
    mut v_inst_3372_: *mut LeanObject,
    mut v_k_3373_: *mut LeanObject,
    mut v_motive_3374_: *mut LeanObject,
    mut v_l_3375_: *mut LeanObject,
    mut v_f_3376_: *mut LeanObject,
    mut v_h__1_3377_: *mut LeanObject,
    mut v_h__2_3378_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_3375_) == 0 {
        let mut v_size_3379_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3380_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_3381_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_3382_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_3383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_3377_);
        v_size_3379_ = lean_ctor_get(v_l_3375_, 0);
        lean_inc(v_size_3379_);
        v_k_3380_ = lean_ctor_get(v_l_3375_, 1);
        lean_inc(v_k_3380_);
        v_v_3381_ = lean_ctor_get(v_l_3375_, 2);
        lean_inc(v_v_3381_);
        v_l_3382_ = lean_ctor_get(v_l_3375_, 3);
        lean_inc(v_l_3382_);
        v_r_3383_ = lean_ctor_get(v_l_3375_, 4);
        lean_inc(v_r_3383_);
        lean_dec_ref_known(v_l_3375_, 5);
        v___x_3384_ = lean_apply_6(
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
        let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_3378_);
        v___x_3385_ = lean_apply_1(v_h__1_3377_, v_f_3376_);
        return v___x_3385_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter___boxed(
    mut v_00_u03b1_3386_: *mut LeanObject,
    mut v_00_u03b2_3387_: *mut LeanObject,
    mut v_00_u03b4_3388_: *mut LeanObject,
    mut v_inst_3389_: *mut LeanObject,
    mut v_k_3390_: *mut LeanObject,
    mut v_motive_3391_: *mut LeanObject,
    mut v_l_3392_: *mut LeanObject,
    mut v_f_3393_: *mut LeanObject,
    mut v_h__1_3394_: *mut LeanObject,
    mut v_h__2_3395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3396_: *mut LeanObject = core::ptr::null_mut();
    v_res_3396_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyCell_match__1_splitter(v_00_u03b1_3386_, v_00_u03b2_3387_, v_00_u03b4_3388_, v_inst_3389_, v_k_3390_, v_motive_3391_, v_l_3392_, v_f_3393_, v_h__1_3394_, v_h__2_3395_);
    lean_dec(v_k_3390_);
    lean_dec_ref(v_inst_3389_);
    return v_res_3396_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(
    mut v_x_3397_: u8,
    mut v_h__1_3398_: *mut LeanObject,
    mut v_h__2_3399_: *mut LeanObject,
    mut v_h__3_3400_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_3397_ {
        0 => {
            let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3400_);
            lean_dec(v_h__2_3399_);
            v___x_3401_ = lean_apply_1(v_h__1_3398_, lean_box(0));
            return v___x_3401_;
        }
        1 => {
            let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3400_);
            lean_dec(v_h__1_3398_);
            v___x_3402_ = lean_apply_1(v_h__2_3399_, lean_box(0));
            return v___x_3402_;
        }
        _ => {
            let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_3399_);
            lean_dec(v_h__1_3398_);
            v___x_3403_ = lean_apply_1(v_h__3_3400_, lean_box(0));
            return v___x_3403_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg___boxed(
    mut v_x_3404_: *mut LeanObject,
    mut v_h__1_3405_: *mut LeanObject,
    mut v_h__2_3406_: *mut LeanObject,
    mut v_h__3_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_3408_: u8 = 0;
    let mut v_res_3409_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_3408_ = (lean_unbox(v_x_3404_) as u8);
    v_res_3409_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___redArg(v_x_33__boxed_3408_, v_h__1_3405_, v_h__2_3406_, v_h__3_3407_);
    return v_res_3409_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(
    mut v_motive_3410_: *mut LeanObject,
    mut v_x_3411_: u8,
    mut v_h__1_3412_: *mut LeanObject,
    mut v_h__2_3413_: *mut LeanObject,
    mut v_h__3_3414_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_3411_ {
        0 => {
            let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3414_);
            lean_dec(v_h__2_3413_);
            v___x_3415_ = lean_apply_1(v_h__1_3412_, lean_box(0));
            return v___x_3415_;
        }
        1 => {
            let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_3414_);
            lean_dec(v_h__1_3412_);
            v___x_3416_ = lean_apply_1(v_h__2_3413_, lean_box(0));
            return v___x_3416_;
        }
        _ => {
            let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_3413_);
            lean_dec(v_h__1_3412_);
            v___x_3417_ = lean_apply_1(v_h__3_3414_, lean_box(0));
            return v___x_3417_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter___boxed(
    mut v_motive_3418_: *mut LeanObject,
    mut v_x_3419_: *mut LeanObject,
    mut v_h__1_3420_: *mut LeanObject,
    mut v_h__2_3421_: *mut LeanObject,
    mut v_h__3_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_42__boxed_3423_: u8 = 0;
    let mut v_res_3424_: *mut LeanObject = core::ptr::null_mut();
    v_x_42__boxed_3423_ = (lean_unbox(v_x_3419_) as u8);
    v_res_3424_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__1_splitter(v_motive_3418_, v_x_42__boxed_3423_, v_h__1_3420_, v_h__2_3421_, v_h__3_3422_);
    return v_res_3424_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___redArg(
    mut v_m_3425_: *mut LeanObject,
    mut v_h__1_3426_: *mut LeanObject,
    mut v_h__2_3427_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_3425_) == 0 {
        let mut v_size_3428_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3429_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_3430_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_3431_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_3432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_3426_);
        v_size_3428_ = lean_ctor_get(v_m_3425_, 0);
        lean_inc(v_size_3428_);
        v_k_3429_ = lean_ctor_get(v_m_3425_, 1);
        lean_inc(v_k_3429_);
        v_v_3430_ = lean_ctor_get(v_m_3425_, 2);
        lean_inc(v_v_3430_);
        v_l_3431_ = lean_ctor_get(v_m_3425_, 3);
        lean_inc(v_l_3431_);
        v_r_3432_ = lean_ctor_get(v_m_3425_, 4);
        lean_inc(v_r_3432_);
        lean_dec_ref_known(v_m_3425_, 5);
        v___x_3433_ = lean_apply_6(
            v_h__2_3427_,
            v_size_3428_,
            v_k_3429_,
            v_v_3430_,
            v_l_3431_,
            v_r_3432_,
            lean_box(0),
        );
        return v___x_3433_;
    } else {
        let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_3427_);
        v___x_3434_ = lean_apply_1(v_h__1_3426_, lean_box(0));
        return v___x_3434_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(
    mut v_00_u03b1_3435_: *mut LeanObject,
    mut v_00_u03b2_3436_: *mut LeanObject,
    mut v_inst_3437_: *mut LeanObject,
    mut v_k_3438_: *mut LeanObject,
    mut v_l_3439_: *mut LeanObject,
    mut v_motive_3440_: *mut LeanObject,
    mut v_m_3441_: *mut LeanObject,
    mut v_hm_3442_: *mut LeanObject,
    mut v_h__1_3443_: *mut LeanObject,
    mut v_h__2_3444_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_3441_) == 0 {
        let mut v_size_3445_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3446_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_3447_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_3448_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_3449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_3443_);
        v_size_3445_ = lean_ctor_get(v_m_3441_, 0);
        lean_inc(v_size_3445_);
        v_k_3446_ = lean_ctor_get(v_m_3441_, 1);
        lean_inc(v_k_3446_);
        v_v_3447_ = lean_ctor_get(v_m_3441_, 2);
        lean_inc(v_v_3447_);
        v_l_3448_ = lean_ctor_get(v_m_3441_, 3);
        lean_inc(v_l_3448_);
        v_r_3449_ = lean_ctor_get(v_m_3441_, 4);
        lean_inc(v_r_3449_);
        lean_dec_ref_known(v_m_3441_, 5);
        v___x_3450_ = lean_apply_6(
            v_h__2_3444_,
            v_size_3445_,
            v_k_3446_,
            v_v_3447_,
            v_l_3448_,
            v_r_3449_,
            lean_box(0),
        );
        return v___x_3450_;
    } else {
        let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_3444_);
        v___x_3451_ = lean_apply_1(v_h__1_3443_, lean_box(0));
        return v___x_3451_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter___boxed(
    mut v_00_u03b1_3452_: *mut LeanObject,
    mut v_00_u03b2_3453_: *mut LeanObject,
    mut v_inst_3454_: *mut LeanObject,
    mut v_k_3455_: *mut LeanObject,
    mut v_l_3456_: *mut LeanObject,
    mut v_motive_3457_: *mut LeanObject,
    mut v_m_3458_: *mut LeanObject,
    mut v_hm_3459_: *mut LeanObject,
    mut v_h__1_3460_: *mut LeanObject,
    mut v_h__2_3461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3462_: *mut LeanObject = core::ptr::null_mut();
    v_res_3462_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_applyPartition_go_match__3_splitter(v_00_u03b1_3452_, v_00_u03b2_3453_, v_inst_3454_, v_k_3455_, v_l_3456_, v_motive_3457_, v_m_3458_, v_hm_3459_, v_h__1_3460_, v_h__2_3461_);
    lean_dec(v_l_3456_);
    lean_dec_ref(v_k_3455_);
    lean_dec_ref(v_inst_3454_);
    return v_res_3462_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(
    mut v_x_3463_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3463_) {
        0 => {
            let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
            v___x_3464_ = lean_unsigned_to_nat(0);
            return v___x_3464_;
        }
        1 => {
            let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
            v___x_3465_ = lean_unsigned_to_nat(1);
            return v___x_3465_;
        }
        _ => {
            let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
            v___x_3466_ = lean_unsigned_to_nat(2);
            return v___x_3466_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg___boxed(
    mut v_x_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3468_: *mut LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(v_x_3467_);
    lean_dec_ref(v_x_3467_);
    return v_res_3468_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(
    mut v_00_u03b1_3469_: *mut LeanObject,
    mut v_00_u03b2_3470_: *mut LeanObject,
    mut v_inst_3471_: *mut LeanObject,
    mut v_k_3472_: *mut LeanObject,
    mut v_x_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    v___x_3474_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___redArg(v_x_3473_);
    return v___x_3474_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx___boxed(
    mut v_00_u03b1_3475_: *mut LeanObject,
    mut v_00_u03b2_3476_: *mut LeanObject,
    mut v_inst_3477_: *mut LeanObject,
    mut v_k_3478_: *mut LeanObject,
    mut v_x_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3480_: *mut LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorIdx(
        v_00_u03b1_3475_,
        v_00_u03b2_3476_,
        v_inst_3477_,
        v_k_3478_,
        v_x_3479_,
    );
    lean_dec_ref(v_x_3479_);
    lean_dec_ref(v_k_3478_);
    lean_dec_ref(v_inst_3477_);
    return v_res_3480_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(
    mut v_t_3481_: *mut LeanObject,
    mut v_k_3482_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_3481_) {
        0 => {
            let mut v_a_3483_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_3484_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_3485_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
            v_a_3483_ = lean_ctor_get(v_t_3481_, 0);
            lean_inc(v_a_3483_);
            v_a_3484_ = lean_ctor_get(v_t_3481_, 1);
            lean_inc(v_a_3484_);
            v_a_3485_ = lean_ctor_get(v_t_3481_, 2);
            lean_inc(v_a_3485_);
            lean_dec_ref_known(v_t_3481_, 3);
            v___x_3486_ = lean_apply_4(v_k_3482_, v_a_3483_, lean_box(0), v_a_3484_, v_a_3485_);
            return v___x_3486_;
        }
        1 => {
            let mut v_a_3487_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_3488_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_3489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
            v_a_3487_ = lean_ctor_get(v_t_3481_, 0);
            lean_inc(v_a_3487_);
            v_a_3488_ = lean_ctor_get(v_t_3481_, 1);
            lean_inc(v_a_3488_);
            v_a_3489_ = lean_ctor_get(v_t_3481_, 2);
            lean_inc(v_a_3489_);
            lean_dec_ref_known(v_t_3481_, 3);
            v___x_3490_ = lean_apply_3(v_k_3482_, v_a_3487_, v_a_3488_, v_a_3489_);
            return v___x_3490_;
        }
        _ => {
            let mut v_a_3491_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_3492_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_3493_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
            v_a_3491_ = lean_ctor_get(v_t_3481_, 0);
            lean_inc(v_a_3491_);
            v_a_3492_ = lean_ctor_get(v_t_3481_, 1);
            lean_inc(v_a_3492_);
            v_a_3493_ = lean_ctor_get(v_t_3481_, 2);
            lean_inc(v_a_3493_);
            lean_dec_ref_known(v_t_3481_, 3);
            v___x_3494_ = lean_apply_4(v_k_3482_, v_a_3491_, v_a_3492_, lean_box(0), v_a_3493_);
            return v___x_3494_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim(
    mut v_00_u03b1_3495_: *mut LeanObject,
    mut v_00_u03b2_3496_: *mut LeanObject,
    mut v_inst_3497_: *mut LeanObject,
    mut v_k_3498_: *mut LeanObject,
    mut v_motive_3499_: *mut LeanObject,
    mut v_ctorIdx_3500_: *mut LeanObject,
    mut v_t_3501_: *mut LeanObject,
    mut v_h_3502_: *mut LeanObject,
    mut v_k_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    v___x_3504_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3501_, v_k_3503_);
    return v___x_3504_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___boxed(
    mut v_00_u03b1_3505_: *mut LeanObject,
    mut v_00_u03b2_3506_: *mut LeanObject,
    mut v_inst_3507_: *mut LeanObject,
    mut v_k_3508_: *mut LeanObject,
    mut v_motive_3509_: *mut LeanObject,
    mut v_ctorIdx_3510_: *mut LeanObject,
    mut v_t_3511_: *mut LeanObject,
    mut v_h_3512_: *mut LeanObject,
    mut v_k_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3514_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_ctorIdx_3510_);
    lean_dec_ref(v_k_3508_);
    lean_dec_ref(v_inst_3507_);
    return v_res_3514_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___redArg(
    mut v_t_3515_: *mut LeanObject,
    mut v_lt_3516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    v___x_3517_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3515_, v_lt_3516_);
    return v___x_3517_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim(
    mut v_00_u03b1_3518_: *mut LeanObject,
    mut v_00_u03b2_3519_: *mut LeanObject,
    mut v_inst_3520_: *mut LeanObject,
    mut v_k_3521_: *mut LeanObject,
    mut v_motive_3522_: *mut LeanObject,
    mut v_t_3523_: *mut LeanObject,
    mut v_h_3524_: *mut LeanObject,
    mut v_lt_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    v___x_3526_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3523_, v_lt_3525_);
    return v___x_3526_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_lt_elim___boxed(
    mut v_00_u03b1_3527_: *mut LeanObject,
    mut v_00_u03b2_3528_: *mut LeanObject,
    mut v_inst_3529_: *mut LeanObject,
    mut v_k_3530_: *mut LeanObject,
    mut v_motive_3531_: *mut LeanObject,
    mut v_t_3532_: *mut LeanObject,
    mut v_h_3533_: *mut LeanObject,
    mut v_lt_3534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3535_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_k_3530_);
    lean_dec_ref(v_inst_3529_);
    return v_res_3535_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___redArg(
    mut v_t_3536_: *mut LeanObject,
    mut v_eq_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    v___x_3538_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3536_, v_eq_3537_);
    return v___x_3538_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim(
    mut v_00_u03b1_3539_: *mut LeanObject,
    mut v_00_u03b2_3540_: *mut LeanObject,
    mut v_inst_3541_: *mut LeanObject,
    mut v_k_3542_: *mut LeanObject,
    mut v_motive_3543_: *mut LeanObject,
    mut v_t_3544_: *mut LeanObject,
    mut v_h_3545_: *mut LeanObject,
    mut v_eq_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    v___x_3547_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3544_, v_eq_3546_);
    return v___x_3547_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_eq_elim___boxed(
    mut v_00_u03b1_3548_: *mut LeanObject,
    mut v_00_u03b2_3549_: *mut LeanObject,
    mut v_inst_3550_: *mut LeanObject,
    mut v_k_3551_: *mut LeanObject,
    mut v_motive_3552_: *mut LeanObject,
    mut v_t_3553_: *mut LeanObject,
    mut v_h_3554_: *mut LeanObject,
    mut v_eq_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3556_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_k_3551_);
    lean_dec_ref(v_inst_3550_);
    return v_res_3556_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___redArg(
    mut v_t_3557_: *mut LeanObject,
    mut v_gt_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    v___x_3559_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3557_, v_gt_3558_);
    return v___x_3559_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim(
    mut v_00_u03b1_3560_: *mut LeanObject,
    mut v_00_u03b2_3561_: *mut LeanObject,
    mut v_inst_3562_: *mut LeanObject,
    mut v_k_3563_: *mut LeanObject,
    mut v_motive_3564_: *mut LeanObject,
    mut v_t_3565_: *mut LeanObject,
    mut v_h_3566_: *mut LeanObject,
    mut v_gt_3567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    v___x_3568_ =
        l_Std_DTreeMap_Internal_Impl_ExplorationStep_ctorElim___redArg(v_t_3565_, v_gt_3567_);
    return v___x_3568_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ExplorationStep_gt_elim___boxed(
    mut v_00_u03b1_3569_: *mut LeanObject,
    mut v_00_u03b2_3570_: *mut LeanObject,
    mut v_inst_3571_: *mut LeanObject,
    mut v_k_3572_: *mut LeanObject,
    mut v_motive_3573_: *mut LeanObject,
    mut v_t_3574_: *mut LeanObject,
    mut v_h_3575_: *mut LeanObject,
    mut v_gt_3576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3577_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_k_3572_);
    lean_dec_ref(v_inst_3571_);
    return v_res_3577_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_explore___redArg(
    mut v_k_3581_: *mut LeanObject,
    mut v_init_3582_: *mut LeanObject,
    mut v_inner_3583_: *mut LeanObject,
    mut v_l_3584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_l_3584_) == 0 {
                    v_k_3585_ = lean_ctor_get(v_l_3584_, 1);
                    lean_inc_n(v_k_3585_, 2);
                    v_v_3586_ = lean_ctor_get(v_l_3584_, 2);
                    lean_inc(v_v_3586_);
                    v_l_3587_ = lean_ctor_get(v_l_3584_, 3);
                    lean_inc(v_l_3587_);
                    v_r_3588_ = lean_ctor_get(v_l_3584_, 4);
                    lean_inc(v_r_3588_);
                    lean_dec_ref_known(v_l_3584_, 5);
                    lean_inc_ref(v_k_3581_);
                    v___x_3589_ = lean_apply_1(v_k_3581_, v_k_3585_);
                    v___x_3590_ = (lean_unbox(v___x_3589_) as u8);
                    match v___x_3590_ {
                        0 => {
                            v___x_3591_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_3588_);
                            lean_dec(v_r_3588_);
                            v___x_3592_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_3592_, 0, v_k_3585_);
                            lean_ctor_set(v___x_3592_, 1, v_v_3586_);
                            lean_ctor_set(v___x_3592_, 2, v___x_3591_);
                            lean_inc(v_inner_3583_);
                            v___x_3593_ = lean_apply_2(v_inner_3583_, v_init_3582_, v___x_3592_);
                            v_init_3582_ = v___x_3593_;
                            v_l_3584_ = v_l_3587_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec_ref(v_k_3581_);
                            v___x_3595_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_3587_);
                            lean_dec(v_l_3587_);
                            v___x_3596_ =
                                l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_3585_, v_v_3586_);
                            v___x_3597_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_3588_);
                            lean_dec(v_r_3588_);
                            v___x_3598_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_3598_, 0, v___x_3595_);
                            lean_ctor_set(v___x_3598_, 1, v___x_3596_);
                            lean_ctor_set(v___x_3598_, 2, v___x_3597_);
                            v___x_3599_ = lean_apply_2(v_inner_3583_, v_init_3582_, v___x_3598_);
                            return v___x_3599_;
                        }
                        _ => {
                            v___x_3600_ =
                                l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_3587_);
                            lean_dec(v_l_3587_);
                            v___x_3601_ = lean_alloc_ctor(2, 3, (0) as u32);
                            lean_ctor_set(v___x_3601_, 0, v___x_3600_);
                            lean_ctor_set(v___x_3601_, 1, v_k_3585_);
                            lean_ctor_set(v___x_3601_, 2, v_v_3586_);
                            lean_inc(v_inner_3583_);
                            v___x_3602_ = lean_apply_2(v_inner_3583_, v_init_3582_, v___x_3601_);
                            v_init_3582_ = v___x_3602_;
                            v_l_3584_ = v_r_3588_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_k_3581_);
                    v___x_3604_ = l_Std_DTreeMap_Internal_Impl_explore___redArg___closed__0;
                    v___x_3605_ = lean_apply_2(v_inner_3583_, v_init_3582_, v___x_3604_);
                    return v___x_3605_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_explore(
    mut v_00_u03b1_3606_: *mut LeanObject,
    mut v_00_u03b2_3607_: *mut LeanObject,
    mut v_00_u03b3_3608_: *mut LeanObject,
    mut v_inst_3609_: *mut LeanObject,
    mut v_k_3610_: *mut LeanObject,
    mut v_init_3611_: *mut LeanObject,
    mut v_inner_3612_: *mut LeanObject,
    mut v_l_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    v___x_3614_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(
        v_k_3610_,
        v_init_3611_,
        v_inner_3612_,
        v_l_3613_,
    );
    return v___x_3614_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_explore___boxed(
    mut v_00_u03b1_3615_: *mut LeanObject,
    mut v_00_u03b2_3616_: *mut LeanObject,
    mut v_00_u03b3_3617_: *mut LeanObject,
    mut v_inst_3618_: *mut LeanObject,
    mut v_k_3619_: *mut LeanObject,
    mut v_init_3620_: *mut LeanObject,
    mut v_inner_3621_: *mut LeanObject,
    mut v_l_3622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3623_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3618_);
    return v_res_3623_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(
    mut v_c_3624_: *mut LeanObject,
    mut v_x_3625_: *mut LeanObject,
) -> u8 {
    let mut v___x_3626_: u8 = 0;
    v___x_3626_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_3624_);
    return v___x_3626_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0___boxed(
    mut v_c_3627_: *mut LeanObject,
    mut v_x_3628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3629_: u8 = 0;
    let mut v_r_3630_: *mut LeanObject = core::ptr::null_mut();
    v_res_3629_ =
        l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___lam__0(v_c_3627_, v_x_3628_);
    lean_dec(v_c_3627_);
    v_r_3630_ = lean_box((v_res_3629_) as usize);
    return v_r_3630_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(
    mut v_inst_3632_: *mut LeanObject,
    mut v_l_3633_: *mut LeanObject,
    mut v_k_3634_: *mut LeanObject,
) -> u8 {
    let mut v___f_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: u8 = 0;
    v___f_3635_ = l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___closed__0;
    v___x_3636_ = l_Std_DTreeMap_Internal_Impl_applyCell___redArg(
        v_inst_3632_,
        v_k_3634_,
        v_l_3633_,
        v___f_3635_,
    );
    v___x_3637_ = (lean_unbox(v___x_3636_) as u8);
    lean_dec(v___x_3636_);
    return v___x_3637_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg___boxed(
    mut v_inst_3638_: *mut LeanObject,
    mut v_l_3639_: *mut LeanObject,
    mut v_k_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3641_: u8 = 0;
    let mut v_r_3642_: *mut LeanObject = core::ptr::null_mut();
    v_res_3641_ =
        l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_3638_, v_l_3639_, v_k_3640_);
    v_r_3642_ = lean_box((v_res_3641_) as usize);
    return v_r_3642_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098(
    mut v_00_u03b1_3643_: *mut LeanObject,
    mut v_00_u03b2_3644_: *mut LeanObject,
    mut v_inst_3645_: *mut LeanObject,
    mut v_l_3646_: *mut LeanObject,
    mut v_k_3647_: *mut LeanObject,
) -> u8 {
    let mut v___x_3648_: u8 = 0;
    v___x_3648_ =
        l_Std_DTreeMap_Internal_Impl_contains_u2098___redArg(v_inst_3645_, v_l_3646_, v_k_3647_);
    return v___x_3648_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains_u2098___boxed(
    mut v_00_u03b1_3649_: *mut LeanObject,
    mut v_00_u03b2_3650_: *mut LeanObject,
    mut v_inst_3651_: *mut LeanObject,
    mut v_l_3652_: *mut LeanObject,
    mut v_k_3653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3654_: u8 = 0;
    let mut v_r_3655_: *mut LeanObject = core::ptr::null_mut();
    v_res_3654_ = l_Std_DTreeMap_Internal_Impl_contains_u2098(
        v_00_u03b1_3649_,
        v_00_u03b2_3650_,
        v_inst_3651_,
        v_l_3652_,
        v_k_3653_,
    );
    v_r_3655_ = lean_box((v_res_3654_) as usize);
    return v_r_3655_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg___lam__0(
    mut v_c_3656_: *mut LeanObject,
    mut v_x_3657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    v___x_3658_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_3656_);
    return v___x_3658_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(
    mut v_inst_3660_: *mut LeanObject,
    mut v_l_3661_: *mut LeanObject,
    mut v_k_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3665_: *mut LeanObject,
    mut v_00_u03b2_3666_: *mut LeanObject,
    mut v_inst_3667_: *mut LeanObject,
    mut v_inst_3668_: *mut LeanObject,
    mut v_inst_3669_: *mut LeanObject,
    mut v_l_3670_: *mut LeanObject,
    mut v_k_3671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    v___x_3672_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_3667_, v_l_3670_, v_k_3671_);
    return v___x_3672_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(
    mut v_inst_3673_: *mut LeanObject,
    mut v_l_3674_: *mut LeanObject,
    mut v_k_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3676_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_3673_, v_l_3674_, v_k_3675_);
    v_val_3677_ = lean_ctor_get(v___x_3676_, 0);
    lean_inc(v_val_3677_);
    lean_dec(v___x_3676_);
    return v_val_3677_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_u2098(
    mut v_00_u03b1_3678_: *mut LeanObject,
    mut v_00_u03b2_3679_: *mut LeanObject,
    mut v_inst_3680_: *mut LeanObject,
    mut v_inst_3681_: *mut LeanObject,
    mut v_inst_3682_: *mut LeanObject,
    mut v_l_3683_: *mut LeanObject,
    mut v_k_3684_: *mut LeanObject,
    mut v_h_3685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    v___x_3686_ =
        l_Std_DTreeMap_Internal_Impl_get_u2098___redArg(v_inst_3680_, v_l_3683_, v_k_3684_);
    return v___x_3686_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    v___x_3690_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___closed__2;
    v___x_3691_ = lean_unsigned_to_nat(14);
    v___x_3692_ = lean_unsigned_to_nat(22);
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
    mut v_inst_3696_: *mut LeanObject,
    mut v_l_3697_: *mut LeanObject,
    mut v_k_3698_: *mut LeanObject,
    mut v_inst_3699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    v___x_3700_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_3696_, v_l_3697_, v_k_3698_);
    if lean_obj_tag(v___x_3700_) == 0 {
        let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
        v___x_3701_ = lean_obj_once(
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
        let mut v_val_3703_: *mut LeanObject = core::ptr::null_mut();
        v_val_3703_ = lean_ctor_get(v___x_3700_, 0);
        lean_inc(v_val_3703_);
        lean_dec_ref_known(v___x_3700_, 1);
        return v_val_3703_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg___boxed(
    mut v_inst_3704_: *mut LeanObject,
    mut v_l_3705_: *mut LeanObject,
    mut v_k_3706_: *mut LeanObject,
    mut v_inst_3707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3708_: *mut LeanObject = core::ptr::null_mut();
    v_res_3708_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(
        v_inst_3704_,
        v_l_3705_,
        v_k_3706_,
        v_inst_3707_,
    );
    lean_dec(v_inst_3707_);
    return v_res_3708_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21_u2098(
    mut v_00_u03b1_3709_: *mut LeanObject,
    mut v_00_u03b2_3710_: *mut LeanObject,
    mut v_inst_3711_: *mut LeanObject,
    mut v_inst_3712_: *mut LeanObject,
    mut v_inst_3713_: *mut LeanObject,
    mut v_l_3714_: *mut LeanObject,
    mut v_k_3715_: *mut LeanObject,
    mut v_inst_3716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    v___x_3717_ = l_Std_DTreeMap_Internal_Impl_get_x21_u2098___redArg(
        v_inst_3711_,
        v_l_3714_,
        v_k_3715_,
        v_inst_3716_,
    );
    return v___x_3717_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21_u2098___boxed(
    mut v_00_u03b1_3718_: *mut LeanObject,
    mut v_00_u03b2_3719_: *mut LeanObject,
    mut v_inst_3720_: *mut LeanObject,
    mut v_inst_3721_: *mut LeanObject,
    mut v_inst_3722_: *mut LeanObject,
    mut v_l_3723_: *mut LeanObject,
    mut v_k_3724_: *mut LeanObject,
    mut v_inst_3725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3726_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_3725_);
    return v_res_3726_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(
    mut v_inst_3727_: *mut LeanObject,
    mut v_k_3728_: *mut LeanObject,
    mut v_l_3729_: *mut LeanObject,
    mut v_fallback_3730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    v___x_3731_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f_u2098___redArg(v_inst_3727_, v_l_3729_, v_k_3728_);
    if lean_obj_tag(v___x_3731_) == 0 {
        lean_inc(v_fallback_3730_);
        return v_fallback_3730_;
    } else {
        let mut v_val_3732_: *mut LeanObject = core::ptr::null_mut();
        v_val_3732_ = lean_ctor_get(v___x_3731_, 0);
        lean_inc(v_val_3732_);
        lean_dec_ref_known(v___x_3731_, 1);
        return v_val_3732_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg___boxed(
    mut v_inst_3733_: *mut LeanObject,
    mut v_k_3734_: *mut LeanObject,
    mut v_l_3735_: *mut LeanObject,
    mut v_fallback_3736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3737_: *mut LeanObject = core::ptr::null_mut();
    v_res_3737_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(
        v_inst_3733_,
        v_k_3734_,
        v_l_3735_,
        v_fallback_3736_,
    );
    lean_dec(v_fallback_3736_);
    return v_res_3737_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD_u2098(
    mut v_00_u03b1_3738_: *mut LeanObject,
    mut v_00_u03b2_3739_: *mut LeanObject,
    mut v_inst_3740_: *mut LeanObject,
    mut v_inst_3741_: *mut LeanObject,
    mut v_inst_3742_: *mut LeanObject,
    mut v_k_3743_: *mut LeanObject,
    mut v_l_3744_: *mut LeanObject,
    mut v_fallback_3745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_Std_DTreeMap_Internal_Impl_getD_u2098___redArg(
        v_inst_3740_,
        v_k_3743_,
        v_l_3744_,
        v_fallback_3745_,
    );
    return v___x_3746_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD_u2098___boxed(
    mut v_00_u03b1_3747_: *mut LeanObject,
    mut v_00_u03b2_3748_: *mut LeanObject,
    mut v_inst_3749_: *mut LeanObject,
    mut v_inst_3750_: *mut LeanObject,
    mut v_inst_3751_: *mut LeanObject,
    mut v_k_3752_: *mut LeanObject,
    mut v_l_3753_: *mut LeanObject,
    mut v_fallback_3754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3755_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_fallback_3754_);
    return v_res_3755_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg___lam__0(
    mut v_c_3756_: *mut LeanObject,
    mut v_x_3757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    v___x_3758_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_3756_);
    return v___x_3758_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
    mut v_inst_3760_: *mut LeanObject,
    mut v_l_3761_: *mut LeanObject,
    mut v_k_3762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3765_: *mut LeanObject,
    mut v_00_u03b2_3766_: *mut LeanObject,
    mut v_inst_3767_: *mut LeanObject,
    mut v_l_3768_: *mut LeanObject,
    mut v_k_3769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    v___x_3770_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
        v_inst_3767_,
        v_l_3768_,
        v_k_3769_,
    );
    return v___x_3770_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(
    mut v_inst_3771_: *mut LeanObject,
    mut v_l_3772_: *mut LeanObject,
    mut v_k_3773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3775_: *mut LeanObject = core::ptr::null_mut();
    v___x_3774_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
        v_inst_3771_,
        v_l_3772_,
        v_k_3773_,
    );
    v_val_3775_ = lean_ctor_get(v___x_3774_, 0);
    lean_inc(v_val_3775_);
    lean_dec(v___x_3774_);
    return v_val_3775_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_u2098(
    mut v_00_u03b1_3776_: *mut LeanObject,
    mut v_00_u03b2_3777_: *mut LeanObject,
    mut v_inst_3778_: *mut LeanObject,
    mut v_l_3779_: *mut LeanObject,
    mut v_k_3780_: *mut LeanObject,
    mut v_h_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    v___x_3782_ =
        l_Std_DTreeMap_Internal_Impl_getEntry_u2098___redArg(v_inst_3778_, v_l_3779_, v_k_3780_);
    return v___x_3782_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(
    mut v_inst_3783_: *mut LeanObject,
    mut v_inst_3784_: *mut LeanObject,
    mut v_l_3785_: *mut LeanObject,
    mut v_k_3786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    v___x_3787_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
        v_inst_3783_,
        v_l_3785_,
        v_k_3786_,
    );
    if lean_obj_tag(v___x_3787_) == 0 {
        let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
        v___x_3788_ = lean_obj_once(
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
        let mut v_val_3790_: *mut LeanObject = core::ptr::null_mut();
        v_val_3790_ = lean_ctor_get(v___x_3787_, 0);
        lean_inc(v_val_3790_);
        lean_dec_ref_known(v___x_3787_, 1);
        return v_val_3790_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg___boxed(
    mut v_inst_3791_: *mut LeanObject,
    mut v_inst_3792_: *mut LeanObject,
    mut v_l_3793_: *mut LeanObject,
    mut v_k_3794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3795_: *mut LeanObject = core::ptr::null_mut();
    v_res_3795_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(
        v_inst_3791_,
        v_inst_3792_,
        v_l_3793_,
        v_k_3794_,
    );
    lean_dec_ref(v_inst_3792_);
    return v_res_3795_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(
    mut v_00_u03b1_3796_: *mut LeanObject,
    mut v_00_u03b2_3797_: *mut LeanObject,
    mut v_inst_3798_: *mut LeanObject,
    mut v_inst_3799_: *mut LeanObject,
    mut v_l_3800_: *mut LeanObject,
    mut v_k_3801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    v___x_3802_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___redArg(
        v_inst_3798_,
        v_inst_3799_,
        v_l_3800_,
        v_k_3801_,
    );
    return v___x_3802_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098___boxed(
    mut v_00_u03b1_3803_: *mut LeanObject,
    mut v_00_u03b2_3804_: *mut LeanObject,
    mut v_inst_3805_: *mut LeanObject,
    mut v_inst_3806_: *mut LeanObject,
    mut v_l_3807_: *mut LeanObject,
    mut v_k_3808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3809_: *mut LeanObject = core::ptr::null_mut();
    v_res_3809_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21_u2098(
        v_00_u03b1_3803_,
        v_00_u03b2_3804_,
        v_inst_3805_,
        v_inst_3806_,
        v_l_3807_,
        v_k_3808_,
    );
    lean_dec_ref(v_inst_3806_);
    return v_res_3809_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(
    mut v_inst_3810_: *mut LeanObject,
    mut v_k_3811_: *mut LeanObject,
    mut v_l_3812_: *mut LeanObject,
    mut v_fallback_3813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    v___x_3814_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f_u2098___redArg(
        v_inst_3810_,
        v_l_3812_,
        v_k_3811_,
    );
    if lean_obj_tag(v___x_3814_) == 0 {
        lean_inc_ref(v_fallback_3813_);
        return v_fallback_3813_;
    } else {
        let mut v_val_3815_: *mut LeanObject = core::ptr::null_mut();
        v_val_3815_ = lean_ctor_get(v___x_3814_, 0);
        lean_inc(v_val_3815_);
        lean_dec_ref_known(v___x_3814_, 1);
        return v_val_3815_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg___boxed(
    mut v_inst_3816_: *mut LeanObject,
    mut v_k_3817_: *mut LeanObject,
    mut v_l_3818_: *mut LeanObject,
    mut v_fallback_3819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3820_: *mut LeanObject = core::ptr::null_mut();
    v_res_3820_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(
        v_inst_3816_,
        v_k_3817_,
        v_l_3818_,
        v_fallback_3819_,
    );
    lean_dec_ref(v_fallback_3819_);
    return v_res_3820_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(
    mut v_00_u03b1_3821_: *mut LeanObject,
    mut v_00_u03b2_3822_: *mut LeanObject,
    mut v_inst_3823_: *mut LeanObject,
    mut v_k_3824_: *mut LeanObject,
    mut v_l_3825_: *mut LeanObject,
    mut v_fallback_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___redArg(
        v_inst_3823_,
        v_k_3824_,
        v_l_3825_,
        v_fallback_3826_,
    );
    return v___x_3827_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD_u2098___boxed(
    mut v_00_u03b1_3828_: *mut LeanObject,
    mut v_00_u03b2_3829_: *mut LeanObject,
    mut v_inst_3830_: *mut LeanObject,
    mut v_k_3831_: *mut LeanObject,
    mut v_l_3832_: *mut LeanObject,
    mut v_fallback_3833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3834_: *mut LeanObject = core::ptr::null_mut();
    v_res_3834_ = l_Std_DTreeMap_Internal_Impl_getEntryD_u2098(
        v_00_u03b1_3828_,
        v_00_u03b2_3829_,
        v_inst_3830_,
        v_k_3831_,
        v_l_3832_,
        v_fallback_3833_,
    );
    lean_dec_ref(v_fallback_3833_);
    return v_res_3834_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg___lam__0(
    mut v_c_3835_: *mut LeanObject,
    mut v_x_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    v___x_3837_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_3835_);
    return v___x_3837_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(
    mut v_inst_3839_: *mut LeanObject,
    mut v_l_3840_: *mut LeanObject,
    mut v_k_3841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3844_: *mut LeanObject,
    mut v_00_u03b2_3845_: *mut LeanObject,
    mut v_inst_3846_: *mut LeanObject,
    mut v_l_3847_: *mut LeanObject,
    mut v_k_3848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    v___x_3849_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_3846_, v_l_3847_, v_k_3848_);
    return v___x_3849_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(
    mut v_inst_3850_: *mut LeanObject,
    mut v_l_3851_: *mut LeanObject,
    mut v_k_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3854_: *mut LeanObject = core::ptr::null_mut();
    v___x_3853_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_3850_, v_l_3851_, v_k_3852_);
    v_val_3854_ = lean_ctor_get(v___x_3853_, 0);
    lean_inc(v_val_3854_);
    lean_dec(v___x_3853_);
    return v_val_3854_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_u2098(
    mut v_00_u03b1_3855_: *mut LeanObject,
    mut v_00_u03b2_3856_: *mut LeanObject,
    mut v_inst_3857_: *mut LeanObject,
    mut v_l_3858_: *mut LeanObject,
    mut v_k_3859_: *mut LeanObject,
    mut v_h_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    v___x_3861_ =
        l_Std_DTreeMap_Internal_Impl_getKey_u2098___redArg(v_inst_3857_, v_l_3858_, v_k_3859_);
    return v___x_3861_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(
    mut v_inst_3862_: *mut LeanObject,
    mut v_l_3863_: *mut LeanObject,
    mut v_k_3864_: *mut LeanObject,
    mut v_inst_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    v___x_3866_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_3862_, v_l_3863_, v_k_3864_);
    if lean_obj_tag(v___x_3866_) == 0 {
        let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
        v___x_3867_ = lean_obj_once(
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
        let mut v_val_3869_: *mut LeanObject = core::ptr::null_mut();
        v_val_3869_ = lean_ctor_get(v___x_3866_, 0);
        lean_inc(v_val_3869_);
        lean_dec_ref_known(v___x_3866_, 1);
        return v_val_3869_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg___boxed(
    mut v_inst_3870_: *mut LeanObject,
    mut v_l_3871_: *mut LeanObject,
    mut v_k_3872_: *mut LeanObject,
    mut v_inst_3873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3874_: *mut LeanObject = core::ptr::null_mut();
    v_res_3874_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(
        v_inst_3870_,
        v_l_3871_,
        v_k_3872_,
        v_inst_3873_,
    );
    lean_dec(v_inst_3873_);
    return v_res_3874_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(
    mut v_00_u03b1_3875_: *mut LeanObject,
    mut v_00_u03b2_3876_: *mut LeanObject,
    mut v_inst_3877_: *mut LeanObject,
    mut v_l_3878_: *mut LeanObject,
    mut v_k_3879_: *mut LeanObject,
    mut v_inst_3880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    v___x_3881_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___redArg(
        v_inst_3877_,
        v_l_3878_,
        v_k_3879_,
        v_inst_3880_,
    );
    return v___x_3881_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098___boxed(
    mut v_00_u03b1_3882_: *mut LeanObject,
    mut v_00_u03b2_3883_: *mut LeanObject,
    mut v_inst_3884_: *mut LeanObject,
    mut v_l_3885_: *mut LeanObject,
    mut v_k_3886_: *mut LeanObject,
    mut v_inst_3887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3888_: *mut LeanObject = core::ptr::null_mut();
    v_res_3888_ = l_Std_DTreeMap_Internal_Impl_getKey_x21_u2098(
        v_00_u03b1_3882_,
        v_00_u03b2_3883_,
        v_inst_3884_,
        v_l_3885_,
        v_k_3886_,
        v_inst_3887_,
    );
    lean_dec(v_inst_3887_);
    return v_res_3888_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(
    mut v_inst_3889_: *mut LeanObject,
    mut v_k_3890_: *mut LeanObject,
    mut v_l_3891_: *mut LeanObject,
    mut v_fallback_3892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    v___x_3893_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f_u2098___redArg(v_inst_3889_, v_l_3891_, v_k_3890_);
    if lean_obj_tag(v___x_3893_) == 0 {
        lean_inc(v_fallback_3892_);
        return v_fallback_3892_;
    } else {
        let mut v_val_3894_: *mut LeanObject = core::ptr::null_mut();
        v_val_3894_ = lean_ctor_get(v___x_3893_, 0);
        lean_inc(v_val_3894_);
        lean_dec_ref_known(v___x_3893_, 1);
        return v_val_3894_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg___boxed(
    mut v_inst_3895_: *mut LeanObject,
    mut v_k_3896_: *mut LeanObject,
    mut v_l_3897_: *mut LeanObject,
    mut v_fallback_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3899_: *mut LeanObject = core::ptr::null_mut();
    v_res_3899_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(
        v_inst_3895_,
        v_k_3896_,
        v_l_3897_,
        v_fallback_3898_,
    );
    lean_dec(v_fallback_3898_);
    return v_res_3899_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(
    mut v_00_u03b1_3900_: *mut LeanObject,
    mut v_00_u03b2_3901_: *mut LeanObject,
    mut v_inst_3902_: *mut LeanObject,
    mut v_k_3903_: *mut LeanObject,
    mut v_l_3904_: *mut LeanObject,
    mut v_fallback_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    v___x_3906_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___redArg(
        v_inst_3902_,
        v_k_3903_,
        v_l_3904_,
        v_fallback_3905_,
    );
    return v___x_3906_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD_u2098___boxed(
    mut v_00_u03b1_3907_: *mut LeanObject,
    mut v_00_u03b2_3908_: *mut LeanObject,
    mut v_inst_3909_: *mut LeanObject,
    mut v_k_3910_: *mut LeanObject,
    mut v_l_3911_: *mut LeanObject,
    mut v_fallback_3912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3913_: *mut LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_Std_DTreeMap_Internal_Impl_getKeyD_u2098(
        v_00_u03b1_3907_,
        v_00_u03b2_3908_,
        v_inst_3909_,
        v_k_3910_,
        v_l_3911_,
        v_fallback_3912_,
    );
    lean_dec(v_fallback_3912_);
    return v_res_3913_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(
    mut v_x_3914_: *mut LeanObject,
) -> u8 {
    let mut v___x_3915_: u8 = 0;
    v___x_3915_ = 0;
    return v___x_3915_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0___boxed(
    mut v_x_3916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3917_: u8 = 0;
    let mut v_r_3918_: *mut LeanObject = core::ptr::null_mut();
    v_res_3917_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__0(v_x_3916_);
    lean_dec(v_x_3916_);
    v_r_3918_ = lean_box((v_res_3917_) as usize);
    return v_r_3918_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(
    mut v_sofar_3919_: *mut LeanObject,
    mut v_step_3920_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_step_3920_) == 0 {
        let mut v_a_3921_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_3922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
        v_a_3921_ = lean_ctor_get(v_step_3920_, 0);
        v_a_3922_ = lean_ctor_get(v_step_3920_, 1);
        lean_inc(v_a_3922_);
        lean_inc(v_a_3921_);
        v___x_3923_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3923_, 0, v_a_3921_);
        lean_ctor_set(v___x_3923_, 1, v_a_3922_);
        v___x_3924_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3924_, 0, v___x_3923_);
        return v___x_3924_;
    } else {
        let mut v_a_3925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
        v_a_3925_ = lean_ctor_get(v_step_3920_, 2);
        v___x_3926_ = l_List_head_x3f___redArg(v_a_3925_);
        if lean_obj_tag(v___x_3926_) == 0 {
            lean_inc(v_sofar_3919_);
            return v_sofar_3919_;
        } else {
            return v___x_3926_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1___boxed(
    mut v_sofar_3927_: *mut LeanObject,
    mut v_step_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3929_: *mut LeanObject = core::ptr::null_mut();
    v_res_3929_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___lam__1(
        v_sofar_3927_,
        v_step_3928_,
    );
    lean_dec_ref(v_step_3928_);
    lean_dec(v_sofar_3927_);
    return v_res_3929_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(
    mut v_l_3932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    v___f_3933_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0;
    v___f_3934_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__1;
    v___x_3935_ = lean_box(0);
    v___x_3936_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(
        v___f_3933_,
        v___x_3935_,
        v___f_3934_,
        v_l_3932_,
    );
    return v___x_3936_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(
    mut v_00_u03b1_3937_: *mut LeanObject,
    mut v_00_u03b2_3938_: *mut LeanObject,
    mut v_inst_3939_: *mut LeanObject,
    mut v_l_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    v___x_3941_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg(v_l_3940_);
    return v___x_3941_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___boxed(
    mut v_00_u03b1_3942_: *mut LeanObject,
    mut v_00_u03b2_3943_: *mut LeanObject,
    mut v_inst_3944_: *mut LeanObject,
    mut v_l_3945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3946_: *mut LeanObject = core::ptr::null_mut();
    v_res_3946_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27(
        v_00_u03b1_3942_,
        v_00_u03b2_3943_,
        v_inst_3944_,
        v_l_3945_,
    );
    lean_dec_ref(v_inst_3944_);
    return v_res_3946_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(
    mut v_x_3947_: *mut LeanObject,
    mut v_x_3948_: *mut LeanObject,
    mut v_x_3949_: *mut LeanObject,
    mut v_r_3950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_List_head_x3f___redArg(v_r_3950_);
    return v___x_3951_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1___boxed(
    mut v_x_3952_: *mut LeanObject,
    mut v_x_3953_: *mut LeanObject,
    mut v_x_3954_: *mut LeanObject,
    mut v_r_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3956_: *mut LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___lam__1(
        v_x_3952_, v_x_3953_, v_x_3954_, v_r_3955_,
    );
    lean_dec(v_r_3955_);
    lean_dec(v_x_3953_);
    lean_dec(v_x_3952_);
    return v_res_3956_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(
    mut v_l_3958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    v___f_3959_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27___redArg___closed__0;
    v___f_3960_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0;
    v___x_3961_ =
        l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_3959_, v_l_3958_, v___f_3960_);
    return v___x_3961_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(
    mut v_00_u03b1_3962_: *mut LeanObject,
    mut v_00_u03b2_3963_: *mut LeanObject,
    mut v_inst_3964_: *mut LeanObject,
    mut v_l_3965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    v___x_3966_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg(v_l_3965_);
    return v___x_3966_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___boxed(
    mut v_00_u03b1_3967_: *mut LeanObject,
    mut v_00_u03b2_3968_: *mut LeanObject,
    mut v_inst_3969_: *mut LeanObject,
    mut v_l_3970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3971_: *mut LeanObject = core::ptr::null_mut();
    v_res_3971_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098(
        v_00_u03b1_3967_,
        v_00_u03b2_3968_,
        v_inst_3969_,
        v_l_3970_,
    );
    lean_dec_ref(v_inst_3969_);
    return v_res_3971_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_reverse___redArg(
    mut v_x_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3980_: u8 = 0;
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3972_) == 0 {
                    v_size_3973_ = lean_ctor_get(v_x_3972_, 0);
                    v_k_3974_ = lean_ctor_get(v_x_3972_, 1);
                    v_v_3975_ = lean_ctor_get(v_x_3972_, 2);
                    v_l_3976_ = lean_ctor_get(v_x_3972_, 3);
                    v_r_3977_ = lean_ctor_get(v_x_3972_, 4);
                    v_isSharedCheck_3986_ = (!lean_is_exclusive(v_x_3972_)) as u8;
                    if v_isSharedCheck_3986_ == 0 {
                        v___x_3979_ = v_x_3972_;
                        v_isShared_3980_ = v_isSharedCheck_3986_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3977_);
                        lean_inc(v_l_3976_);
                        lean_inc(v_v_3975_);
                        lean_inc(v_k_3974_);
                        lean_inc(v_size_3973_);
                        lean_dec(v_x_3972_);
                        v___x_3979_ = lean_box(0);
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
                    lean_ctor_set(v___x_3979_, 4, v___x_3982_);
                    lean_ctor_set(v___x_3979_, 3, v___x_3981_);
                    v___x_3984_ = v___x_3979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_size_3973_);
                    lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_k_3974_);
                    lean_ctor_set(v_reuseFailAlloc_3985_, 2, v_v_3975_);
                    lean_ctor_set(v_reuseFailAlloc_3985_, 3, v___x_3981_);
                    lean_ctor_set(v_reuseFailAlloc_3985_, 4, v___x_3982_);
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
    mut v_00_u03b1_3987_: *mut LeanObject,
    mut v_00_u03b2_3988_: *mut LeanObject,
    mut v_x_3989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    v___x_3990_ = l_Std_DTreeMap_Internal_Impl_reverse___redArg(v_x_3989_);
    return v___x_3990_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg___lam__0(
    mut v_c_3991_: *mut LeanObject,
    mut v_x_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    v___x_3993_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_3991_);
    return v___x_3993_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
    mut v_inst_3995_: *mut LeanObject,
    mut v_l_3996_: *mut LeanObject,
    mut v_k_3997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4000_: *mut LeanObject,
    mut v_00_u03b2_4001_: *mut LeanObject,
    mut v_inst_4002_: *mut LeanObject,
    mut v_l_4003_: *mut LeanObject,
    mut v_k_4004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    v___x_4005_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
        v_inst_4002_,
        v_l_4003_,
        v_k_4004_,
    );
    return v___x_4005_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(
    mut v_inst_4006_: *mut LeanObject,
    mut v_l_4007_: *mut LeanObject,
    mut v_k_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4010_: *mut LeanObject = core::ptr::null_mut();
    v___x_4009_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
        v_inst_4006_,
        v_l_4007_,
        v_k_4008_,
    );
    v_val_4010_ = lean_ctor_get(v___x_4009_, 0);
    lean_inc(v_val_4010_);
    lean_dec(v___x_4009_);
    return v_val_4010_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_u2098(
    mut v_00_u03b1_4011_: *mut LeanObject,
    mut v_00_u03b2_4012_: *mut LeanObject,
    mut v_inst_4013_: *mut LeanObject,
    mut v_l_4014_: *mut LeanObject,
    mut v_k_4015_: *mut LeanObject,
    mut v_h_4016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    v___x_4017_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_u2098___redArg(v_inst_4013_, v_l_4014_, v_k_4015_);
    return v___x_4017_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(
    mut v_inst_4018_: *mut LeanObject,
    mut v_l_4019_: *mut LeanObject,
    mut v_k_4020_: *mut LeanObject,
    mut v_inst_4021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    v___x_4022_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
        v_inst_4018_,
        v_l_4019_,
        v_k_4020_,
    );
    if lean_obj_tag(v___x_4022_) == 0 {
        let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
        v___x_4023_ = lean_obj_once(
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
        let mut v_val_4025_: *mut LeanObject = core::ptr::null_mut();
        v_val_4025_ = lean_ctor_get(v___x_4022_, 0);
        lean_inc(v_val_4025_);
        lean_dec_ref_known(v___x_4022_, 1);
        return v_val_4025_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg___boxed(
    mut v_inst_4026_: *mut LeanObject,
    mut v_l_4027_: *mut LeanObject,
    mut v_k_4028_: *mut LeanObject,
    mut v_inst_4029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4030_: *mut LeanObject = core::ptr::null_mut();
    v_res_4030_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(
        v_inst_4026_,
        v_l_4027_,
        v_k_4028_,
        v_inst_4029_,
    );
    lean_dec(v_inst_4029_);
    return v_res_4030_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(
    mut v_00_u03b1_4031_: *mut LeanObject,
    mut v_00_u03b2_4032_: *mut LeanObject,
    mut v_inst_4033_: *mut LeanObject,
    mut v_l_4034_: *mut LeanObject,
    mut v_k_4035_: *mut LeanObject,
    mut v_inst_4036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___redArg(
        v_inst_4033_,
        v_l_4034_,
        v_k_4035_,
        v_inst_4036_,
    );
    return v___x_4037_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098___boxed(
    mut v_00_u03b1_4038_: *mut LeanObject,
    mut v_00_u03b2_4039_: *mut LeanObject,
    mut v_inst_4040_: *mut LeanObject,
    mut v_l_4041_: *mut LeanObject,
    mut v_k_4042_: *mut LeanObject,
    mut v_inst_4043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4044_: *mut LeanObject = core::ptr::null_mut();
    v_res_4044_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21_u2098(
        v_00_u03b1_4038_,
        v_00_u03b2_4039_,
        v_inst_4040_,
        v_l_4041_,
        v_k_4042_,
        v_inst_4043_,
    );
    lean_dec(v_inst_4043_);
    return v_res_4044_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(
    mut v_inst_4045_: *mut LeanObject,
    mut v_l_4046_: *mut LeanObject,
    mut v_k_4047_: *mut LeanObject,
    mut v_fallback_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    v___x_4049_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f_u2098___redArg(
        v_inst_4045_,
        v_l_4046_,
        v_k_4047_,
    );
    if lean_obj_tag(v___x_4049_) == 0 {
        lean_inc(v_fallback_4048_);
        return v_fallback_4048_;
    } else {
        let mut v_val_4050_: *mut LeanObject = core::ptr::null_mut();
        v_val_4050_ = lean_ctor_get(v___x_4049_, 0);
        lean_inc(v_val_4050_);
        lean_dec_ref_known(v___x_4049_, 1);
        return v_val_4050_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg___boxed(
    mut v_inst_4051_: *mut LeanObject,
    mut v_l_4052_: *mut LeanObject,
    mut v_k_4053_: *mut LeanObject,
    mut v_fallback_4054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4055_: *mut LeanObject = core::ptr::null_mut();
    v_res_4055_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(
        v_inst_4051_,
        v_l_4052_,
        v_k_4053_,
        v_fallback_4054_,
    );
    lean_dec(v_fallback_4054_);
    return v_res_4055_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(
    mut v_00_u03b1_4056_: *mut LeanObject,
    mut v_00_u03b2_4057_: *mut LeanObject,
    mut v_inst_4058_: *mut LeanObject,
    mut v_l_4059_: *mut LeanObject,
    mut v_k_4060_: *mut LeanObject,
    mut v_fallback_4061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    v___x_4062_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___redArg(
        v_inst_4058_,
        v_l_4059_,
        v_k_4060_,
        v_fallback_4061_,
    );
    return v___x_4062_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD_u2098___boxed(
    mut v_00_u03b1_4063_: *mut LeanObject,
    mut v_00_u03b2_4064_: *mut LeanObject,
    mut v_inst_4065_: *mut LeanObject,
    mut v_l_4066_: *mut LeanObject,
    mut v_k_4067_: *mut LeanObject,
    mut v_fallback_4068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4069_: *mut LeanObject = core::ptr::null_mut();
    v_res_4069_ = l_Std_DTreeMap_Internal_Impl_Const_getD_u2098(
        v_00_u03b1_4063_,
        v_00_u03b2_4064_,
        v_inst_4065_,
        v_l_4066_,
        v_k_4067_,
        v_fallback_4068_,
    );
    lean_dec(v_fallback_4068_);
    return v_res_4069_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(
    mut v_t_4070_: *mut LeanObject,
    mut v_h__1_4071_: *mut LeanObject,
    mut v_h__2_4072_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4070_) == 0 {
        let mut v_size_4073_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4074_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4075_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4076_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4071_);
        v_size_4073_ = lean_ctor_get(v_t_4070_, 0);
        lean_inc(v_size_4073_);
        v_k_4074_ = lean_ctor_get(v_t_4070_, 1);
        lean_inc(v_k_4074_);
        v_v_4075_ = lean_ctor_get(v_t_4070_, 2);
        lean_inc(v_v_4075_);
        v_l_4076_ = lean_ctor_get(v_t_4070_, 3);
        lean_inc(v_l_4076_);
        v_r_4077_ = lean_ctor_get(v_t_4070_, 4);
        lean_inc(v_r_4077_);
        lean_dec_ref_known(v_t_4070_, 5);
        v___x_4078_ = lean_apply_5(
            v_h__2_4072_,
            v_size_4073_,
            v_k_4074_,
            v_v_4075_,
            v_l_4076_,
            v_r_4077_,
        );
        return v___x_4078_;
    } else {
        let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4072_);
        v___x_4079_ = lean_box(0);
        v___x_4080_ = lean_apply_1(v_h__1_4071_, v___x_4079_);
        return v___x_4080_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(
    mut v_00_u03b1_4081_: *mut LeanObject,
    mut v_00_u03b2_4082_: *mut LeanObject,
    mut v_motive_4083_: *mut LeanObject,
    mut v_t_4084_: *mut LeanObject,
    mut v_h__1_4085_: *mut LeanObject,
    mut v_h__2_4086_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4084_) == 0 {
        let mut v_size_4087_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4088_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4089_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4090_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4085_);
        v_size_4087_ = lean_ctor_get(v_t_4084_, 0);
        lean_inc(v_size_4087_);
        v_k_4088_ = lean_ctor_get(v_t_4084_, 1);
        lean_inc(v_k_4088_);
        v_v_4089_ = lean_ctor_get(v_t_4084_, 2);
        lean_inc(v_v_4089_);
        v_l_4090_ = lean_ctor_get(v_t_4084_, 3);
        lean_inc(v_l_4090_);
        v_r_4091_ = lean_ctor_get(v_t_4084_, 4);
        lean_inc(v_r_4091_);
        lean_dec_ref_known(v_t_4084_, 5);
        v___x_4092_ = lean_apply_5(
            v_h__2_4086_,
            v_size_4087_,
            v_k_4088_,
            v_v_4089_,
            v_l_4090_,
            v_r_4091_,
        );
        return v___x_4092_;
    } else {
        let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4086_);
        v___x_4093_ = lean_box(0);
        v___x_4094_ = lean_apply_1(v_h__1_4085_, v___x_4093_);
        return v___x_4094_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(
    mut v_x_4095_: u8,
    mut v_h__1_4096_: *mut LeanObject,
    mut v_h__2_4097_: *mut LeanObject,
    mut v_h__3_4098_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_4095_ {
        0 => {
            let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4098_);
            lean_dec(v_h__2_4097_);
            v___x_4099_ = lean_apply_1(v_h__1_4096_, lean_box(0));
            return v___x_4099_;
        }
        1 => {
            let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_4097_);
            lean_dec(v_h__1_4096_);
            v___x_4100_ = lean_apply_1(v_h__3_4098_, lean_box(0));
            return v___x_4100_;
        }
        _ => {
            let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4098_);
            lean_dec(v_h__1_4096_);
            v___x_4101_ = lean_apply_1(v_h__2_4097_, lean_box(0));
            return v___x_4101_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg___boxed(
    mut v_x_4102_: *mut LeanObject,
    mut v_h__1_4103_: *mut LeanObject,
    mut v_h__2_4104_: *mut LeanObject,
    mut v_h__3_4105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_4106_: u8 = 0;
    let mut v_res_4107_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_4106_ = (lean_unbox(v_x_4102_) as u8);
    v_res_4107_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___redArg(v_x_33__boxed_4106_, v_h__1_4103_, v_h__2_4104_, v_h__3_4105_);
    return v_res_4107_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(
    mut v_motive_4108_: *mut LeanObject,
    mut v_x_4109_: u8,
    mut v_h__1_4110_: *mut LeanObject,
    mut v_h__2_4111_: *mut LeanObject,
    mut v_h__3_4112_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_4109_ {
        0 => {
            let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4112_);
            lean_dec(v_h__2_4111_);
            v___x_4113_ = lean_apply_1(v_h__1_4110_, lean_box(0));
            return v___x_4113_;
        }
        1 => {
            let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_4111_);
            lean_dec(v_h__1_4110_);
            v___x_4114_ = lean_apply_1(v_h__3_4112_, lean_box(0));
            return v___x_4114_;
        }
        _ => {
            let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4112_);
            lean_dec(v_h__1_4110_);
            v___x_4115_ = lean_apply_1(v_h__2_4111_, lean_box(0));
            return v___x_4115_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter___boxed(
    mut v_motive_4116_: *mut LeanObject,
    mut v_x_4117_: *mut LeanObject,
    mut v_h__1_4118_: *mut LeanObject,
    mut v_h__2_4119_: *mut LeanObject,
    mut v_h__3_4120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_42__boxed_4121_: u8 = 0;
    let mut v_res_4122_: *mut LeanObject = core::ptr::null_mut();
    v_x_42__boxed_4121_ = (lean_unbox(v_x_4117_) as u8);
    v_res_4122_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_x3f_match__1_splitter(v_motive_4116_, v_x_42__boxed_4121_, v_h__1_4118_, v_h__2_4119_, v_h__3_4120_);
    return v_res_4122_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter___redArg(
    mut v_x_4123_: *mut LeanObject,
    mut v_h__1_4124_: *mut LeanObject,
    mut v_h__2_4125_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4123_) == 0 {
        let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4125_);
        v___x_4126_ = lean_apply_1(v_h__1_4124_, lean_box(0));
        return v___x_4126_;
    } else {
        let mut v_val_4127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4124_);
        v_val_4127_ = lean_ctor_get(v_x_4123_, 0);
        lean_inc(v_val_4127_);
        lean_dec_ref_known(v_x_4123_, 1);
        v___x_4128_ = lean_apply_2(v_h__2_4125_, v_val_4127_, lean_box(0));
        return v___x_4128_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_get_x3f_match__1_splitter(
    mut v_00_u03b1_4129_: *mut LeanObject,
    mut v_00_u03b2_4130_: *mut LeanObject,
    mut v_motive_4131_: *mut LeanObject,
    mut v_x_4132_: *mut LeanObject,
    mut v_h__1_4133_: *mut LeanObject,
    mut v_h__2_4134_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4132_) == 0 {
        let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4134_);
        v___x_4135_ = lean_apply_1(v_h__1_4133_, lean_box(0));
        return v___x_4135_;
    } else {
        let mut v_val_4136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4133_);
        v_val_4136_ = lean_ctor_get(v_x_4132_, 0);
        lean_inc(v_val_4136_);
        lean_dec_ref_known(v_x_4132_, 1);
        v___x_4137_ = lean_apply_2(v_h__2_4134_, v_val_4136_, lean_box(0));
        return v___x_4137_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___redArg(
    mut v_t_4138_: *mut LeanObject,
    mut v_h__1_4139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    v_size_4140_ = lean_ctor_get(v_t_4138_, 0);
    lean_inc(v_size_4140_);
    v_k_4141_ = lean_ctor_get(v_t_4138_, 1);
    lean_inc(v_k_4141_);
    v_v_4142_ = lean_ctor_get(v_t_4138_, 2);
    lean_inc(v_v_4142_);
    v_l_4143_ = lean_ctor_get(v_t_4138_, 3);
    lean_inc(v_l_4143_);
    v_r_4144_ = lean_ctor_get(v_t_4138_, 4);
    lean_inc(v_r_4144_);
    lean_dec(v_t_4138_);
    v___x_4145_ = lean_apply_6(
        v_h__1_4139_,
        v_size_4140_,
        v_k_4141_,
        v_v_4142_,
        v_l_4143_,
        v_r_4144_,
        lean_box(0),
    );
    return v___x_4145_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(
    mut v_00_u03b1_4146_: *mut LeanObject,
    mut v_00_u03b2_4147_: *mut LeanObject,
    mut v_inst_4148_: *mut LeanObject,
    mut v_k_4149_: *mut LeanObject,
    mut v_motive_4150_: *mut LeanObject,
    mut v_t_4151_: *mut LeanObject,
    mut v_hlk_4152_: *mut LeanObject,
    mut v_h__1_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    v_size_4154_ = lean_ctor_get(v_t_4151_, 0);
    lean_inc(v_size_4154_);
    v_k_4155_ = lean_ctor_get(v_t_4151_, 1);
    lean_inc(v_k_4155_);
    v_v_4156_ = lean_ctor_get(v_t_4151_, 2);
    lean_inc(v_v_4156_);
    v_l_4157_ = lean_ctor_get(v_t_4151_, 3);
    lean_inc(v_l_4157_);
    v_r_4158_ = lean_ctor_get(v_t_4151_, 4);
    lean_inc(v_r_4158_);
    lean_dec(v_t_4151_);
    v___x_4159_ = lean_apply_6(
        v_h__1_4153_,
        v_size_4154_,
        v_k_4155_,
        v_v_4156_,
        v_l_4157_,
        v_r_4158_,
        lean_box(0),
    );
    return v___x_4159_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter___boxed(
    mut v_00_u03b1_4160_: *mut LeanObject,
    mut v_00_u03b2_4161_: *mut LeanObject,
    mut v_inst_4162_: *mut LeanObject,
    mut v_k_4163_: *mut LeanObject,
    mut v_motive_4164_: *mut LeanObject,
    mut v_t_4165_: *mut LeanObject,
    mut v_hlk_4166_: *mut LeanObject,
    mut v_h__1_4167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4168_: *mut LeanObject = core::ptr::null_mut();
    v_res_4168_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_get_match__1_splitter(v_00_u03b1_4160_, v_00_u03b2_4161_, v_inst_4162_, v_k_4163_, v_motive_4164_, v_t_4165_, v_hlk_4166_, v_h__1_4167_);
    lean_dec(v_k_4163_);
    lean_dec_ref(v_inst_4162_);
    return v_res_4168_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_4169_: *mut LeanObject,
    mut v_h__1_4170_: *mut LeanObject,
    mut v_h__2_4171_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4169_) == 0 {
        let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4171_);
        v___x_4172_ = lean_box(0);
        v___x_4173_ = lean_apply_1(v_h__1_4170_, v___x_4172_);
        return v___x_4173_;
    } else {
        let mut v_val_4174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4170_);
        v_val_4174_ = lean_ctor_get(v_x_4169_, 0);
        lean_inc(v_val_4174_);
        lean_dec_ref_known(v_x_4169_, 1);
        v___x_4175_ = lean_apply_1(v_h__2_4171_, v_val_4174_);
        return v___x_4175_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4176_: *mut LeanObject,
    mut v_00_u03b2_4177_: *mut LeanObject,
    mut v_motive_4178_: *mut LeanObject,
    mut v_x_4179_: *mut LeanObject,
    mut v_h__1_4180_: *mut LeanObject,
    mut v_h__2_4181_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4179_) == 0 {
        let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4181_);
        v___x_4182_ = lean_box(0);
        v___x_4183_ = lean_apply_1(v_h__1_4180_, v___x_4182_);
        return v___x_4183_;
    } else {
        let mut v_val_4184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4180_);
        v_val_4184_ = lean_ctor_get(v_x_4179_, 0);
        lean_inc(v_val_4184_);
        lean_dec_ref_known(v_x_4179_, 1);
        v___x_4185_ = lean_apply_1(v_h__2_4181_, v_val_4184_);
        return v___x_4185_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___redArg(
    mut v_t_4186_: *mut LeanObject,
    mut v_h__1_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    v_size_4188_ = lean_ctor_get(v_t_4186_, 0);
    lean_inc(v_size_4188_);
    v_k_4189_ = lean_ctor_get(v_t_4186_, 1);
    lean_inc(v_k_4189_);
    v_v_4190_ = lean_ctor_get(v_t_4186_, 2);
    lean_inc(v_v_4190_);
    v_l_4191_ = lean_ctor_get(v_t_4186_, 3);
    lean_inc(v_l_4191_);
    v_r_4192_ = lean_ctor_get(v_t_4186_, 4);
    lean_inc(v_r_4192_);
    lean_dec(v_t_4186_);
    v___x_4193_ = lean_apply_6(
        v_h__1_4187_,
        v_size_4188_,
        v_k_4189_,
        v_v_4190_,
        v_l_4191_,
        v_r_4192_,
        lean_box(0),
    );
    return v___x_4193_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(
    mut v_00_u03b1_4194_: *mut LeanObject,
    mut v_00_u03b2_4195_: *mut LeanObject,
    mut v_inst_4196_: *mut LeanObject,
    mut v_k_4197_: *mut LeanObject,
    mut v_motive_4198_: *mut LeanObject,
    mut v_t_4199_: *mut LeanObject,
    mut v_hlk_4200_: *mut LeanObject,
    mut v_h__1_4201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    v_size_4202_ = lean_ctor_get(v_t_4199_, 0);
    lean_inc(v_size_4202_);
    v_k_4203_ = lean_ctor_get(v_t_4199_, 1);
    lean_inc(v_k_4203_);
    v_v_4204_ = lean_ctor_get(v_t_4199_, 2);
    lean_inc(v_v_4204_);
    v_l_4205_ = lean_ctor_get(v_t_4199_, 3);
    lean_inc(v_l_4205_);
    v_r_4206_ = lean_ctor_get(v_t_4199_, 4);
    lean_inc(v_r_4206_);
    lean_dec(v_t_4199_);
    v___x_4207_ = lean_apply_6(
        v_h__1_4201_,
        v_size_4202_,
        v_k_4203_,
        v_v_4204_,
        v_l_4205_,
        v_r_4206_,
        lean_box(0),
    );
    return v___x_4207_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter___boxed(
    mut v_00_u03b1_4208_: *mut LeanObject,
    mut v_00_u03b2_4209_: *mut LeanObject,
    mut v_inst_4210_: *mut LeanObject,
    mut v_k_4211_: *mut LeanObject,
    mut v_motive_4212_: *mut LeanObject,
    mut v_t_4213_: *mut LeanObject,
    mut v_hlk_4214_: *mut LeanObject,
    mut v_h__1_4215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4216_: *mut LeanObject = core::ptr::null_mut();
    v_res_4216_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getKey_match__1_splitter(v_00_u03b1_4208_, v_00_u03b2_4209_, v_inst_4210_, v_k_4211_, v_motive_4212_, v_t_4213_, v_hlk_4214_, v_h__1_4215_);
    lean_dec(v_k_4211_);
    lean_dec_ref(v_inst_4210_);
    return v_res_4216_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(
    mut v_x_4217_: *mut LeanObject,
    mut v_h__1_4218_: *mut LeanObject,
    mut v_h__2_4219_: *mut LeanObject,
    mut v_h__3_4220_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4217_) == 0 {
        let mut v_l_4221_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4218_);
        v_l_4221_ = lean_ctor_get(v_x_4217_, 3);
        if lean_obj_tag(v_l_4221_) == 0 {
            let mut v_size_4222_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4223_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4224_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4225_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4226_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4227_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4228_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4229_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4230_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4221_);
            lean_dec(v_h__2_4219_);
            v_size_4222_ = lean_ctor_get(v_x_4217_, 0);
            lean_inc(v_size_4222_);
            v_k_4223_ = lean_ctor_get(v_x_4217_, 1);
            lean_inc(v_k_4223_);
            v_v_4224_ = lean_ctor_get(v_x_4217_, 2);
            lean_inc(v_v_4224_);
            v_r_4225_ = lean_ctor_get(v_x_4217_, 4);
            lean_inc(v_r_4225_);
            lean_dec_ref_known(v_x_4217_, 5);
            v_size_4226_ = lean_ctor_get(v_l_4221_, 0);
            lean_inc(v_size_4226_);
            v_k_4227_ = lean_ctor_get(v_l_4221_, 1);
            lean_inc(v_k_4227_);
            v_v_4228_ = lean_ctor_get(v_l_4221_, 2);
            lean_inc(v_v_4228_);
            v_l_4229_ = lean_ctor_get(v_l_4221_, 3);
            lean_inc(v_l_4229_);
            v_r_4230_ = lean_ctor_get(v_l_4221_, 4);
            lean_inc(v_r_4230_);
            lean_dec_ref_known(v_l_4221_, 5);
            v___x_4231_ = lean_apply_9(
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
            let mut v_size_4232_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4233_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4234_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4235_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4220_);
            v_size_4232_ = lean_ctor_get(v_x_4217_, 0);
            lean_inc(v_size_4232_);
            v_k_4233_ = lean_ctor_get(v_x_4217_, 1);
            lean_inc(v_k_4233_);
            v_v_4234_ = lean_ctor_get(v_x_4217_, 2);
            lean_inc(v_v_4234_);
            v_r_4235_ = lean_ctor_get(v_x_4217_, 4);
            lean_inc(v_r_4235_);
            lean_dec_ref_known(v_x_4217_, 5);
            v___x_4236_ = lean_apply_4(v_h__2_4219_, v_size_4232_, v_k_4233_, v_v_4234_, v_r_4235_);
            return v___x_4236_;
        }
    } else {
        let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4220_);
        lean_dec(v_h__2_4219_);
        v___x_4237_ = lean_box(0);
        v___x_4238_ = lean_apply_1(v_h__1_4218_, v___x_4237_);
        return v___x_4238_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4239_: *mut LeanObject,
    mut v_00_u03b2_4240_: *mut LeanObject,
    mut v_motive_4241_: *mut LeanObject,
    mut v_x_4242_: *mut LeanObject,
    mut v_h__1_4243_: *mut LeanObject,
    mut v_h__2_4244_: *mut LeanObject,
    mut v_h__3_4245_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4242_) == 0 {
        let mut v_l_4246_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4243_);
        v_l_4246_ = lean_ctor_get(v_x_4242_, 3);
        if lean_obj_tag(v_l_4246_) == 0 {
            let mut v_size_4247_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4248_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4249_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4250_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4251_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4252_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4253_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4254_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4255_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4246_);
            lean_dec(v_h__2_4244_);
            v_size_4247_ = lean_ctor_get(v_x_4242_, 0);
            lean_inc(v_size_4247_);
            v_k_4248_ = lean_ctor_get(v_x_4242_, 1);
            lean_inc(v_k_4248_);
            v_v_4249_ = lean_ctor_get(v_x_4242_, 2);
            lean_inc(v_v_4249_);
            v_r_4250_ = lean_ctor_get(v_x_4242_, 4);
            lean_inc(v_r_4250_);
            lean_dec_ref_known(v_x_4242_, 5);
            v_size_4251_ = lean_ctor_get(v_l_4246_, 0);
            lean_inc(v_size_4251_);
            v_k_4252_ = lean_ctor_get(v_l_4246_, 1);
            lean_inc(v_k_4252_);
            v_v_4253_ = lean_ctor_get(v_l_4246_, 2);
            lean_inc(v_v_4253_);
            v_l_4254_ = lean_ctor_get(v_l_4246_, 3);
            lean_inc(v_l_4254_);
            v_r_4255_ = lean_ctor_get(v_l_4246_, 4);
            lean_inc(v_r_4255_);
            lean_dec_ref_known(v_l_4246_, 5);
            v___x_4256_ = lean_apply_9(
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
            let mut v_size_4257_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4258_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4259_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4260_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4245_);
            v_size_4257_ = lean_ctor_get(v_x_4242_, 0);
            lean_inc(v_size_4257_);
            v_k_4258_ = lean_ctor_get(v_x_4242_, 1);
            lean_inc(v_k_4258_);
            v_v_4259_ = lean_ctor_get(v_x_4242_, 2);
            lean_inc(v_v_4259_);
            v_r_4260_ = lean_ctor_get(v_x_4242_, 4);
            lean_inc(v_r_4260_);
            lean_dec_ref_known(v_x_4242_, 5);
            v___x_4261_ = lean_apply_4(v_h__2_4244_, v_size_4257_, v_k_4258_, v_v_4259_, v_r_4260_);
            return v___x_4261_;
        }
    } else {
        let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4245_);
        lean_dec(v_h__2_4244_);
        v___x_4262_ = lean_box(0);
        v___x_4263_ = lean_apply_1(v_h__1_4243_, v___x_4262_);
        return v___x_4263_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___redArg(
    mut v_step_4264_: *mut LeanObject,
    mut v_h__1_4265_: *mut LeanObject,
    mut v_h__2_4266_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_step_4264_) == 0 {
        let mut v_a_4267_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4268_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4266_);
        v_a_4267_ = lean_ctor_get(v_step_4264_, 0);
        lean_inc(v_a_4267_);
        v_a_4268_ = lean_ctor_get(v_step_4264_, 1);
        lean_inc(v_a_4268_);
        v_a_4269_ = lean_ctor_get(v_step_4264_, 2);
        lean_inc(v_a_4269_);
        lean_dec_ref_known(v_step_4264_, 3);
        v___x_4270_ = lean_apply_4(v_h__1_4265_, v_a_4267_, lean_box(0), v_a_4268_, v_a_4269_);
        return v___x_4270_;
    } else {
        let mut v_a_4271_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4272_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4265_);
        v_a_4271_ = lean_ctor_get(v_step_4264_, 0);
        lean_inc(v_a_4271_);
        v_a_4272_ = lean_ctor_get(v_step_4264_, 1);
        lean_inc(v_a_4272_);
        v_a_4273_ = lean_ctor_get(v_step_4264_, 2);
        lean_inc(v_a_4273_);
        lean_dec_ref_known(v_step_4264_, 3);
        v___x_4274_ = lean_apply_3(v_h__2_4266_, v_a_4271_, v_a_4272_, v_a_4273_);
        return v___x_4274_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(
    mut v_00_u03b1_4275_: *mut LeanObject,
    mut v_00_u03b2_4276_: *mut LeanObject,
    mut v_inst_4277_: *mut LeanObject,
    mut v_motive_4278_: *mut LeanObject,
    mut v_step_4279_: *mut LeanObject,
    mut v_h__1_4280_: *mut LeanObject,
    mut v_h__2_4281_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_step_4279_) == 0 {
        let mut v_a_4282_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4283_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4281_);
        v_a_4282_ = lean_ctor_get(v_step_4279_, 0);
        lean_inc(v_a_4282_);
        v_a_4283_ = lean_ctor_get(v_step_4279_, 1);
        lean_inc(v_a_4283_);
        v_a_4284_ = lean_ctor_get(v_step_4279_, 2);
        lean_inc(v_a_4284_);
        lean_dec_ref_known(v_step_4279_, 3);
        v___x_4285_ = lean_apply_4(v_h__1_4280_, v_a_4282_, lean_box(0), v_a_4283_, v_a_4284_);
        return v___x_4285_;
    } else {
        let mut v_a_4286_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4287_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4280_);
        v_a_4286_ = lean_ctor_get(v_step_4279_, 0);
        lean_inc(v_a_4286_);
        v_a_4287_ = lean_ctor_get(v_step_4279_, 1);
        lean_inc(v_a_4287_);
        v_a_4288_ = lean_ctor_get(v_step_4279_, 2);
        lean_inc(v_a_4288_);
        lean_dec_ref_known(v_step_4279_, 3);
        v___x_4289_ = lean_apply_3(v_h__2_4281_, v_a_4286_, v_a_4287_, v_a_4288_);
        return v___x_4289_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter___boxed(
    mut v_00_u03b1_4290_: *mut LeanObject,
    mut v_00_u03b2_4291_: *mut LeanObject,
    mut v_inst_4292_: *mut LeanObject,
    mut v_motive_4293_: *mut LeanObject,
    mut v_step_4294_: *mut LeanObject,
    mut v_h__1_4295_: *mut LeanObject,
    mut v_h__2_4296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4297_: *mut LeanObject = core::ptr::null_mut();
    v_res_4297_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098_x27_match__1_splitter(v_00_u03b1_4290_, v_00_u03b2_4291_, v_inst_4292_, v_motive_4293_, v_step_4294_, v_h__1_4295_, v_h__2_4296_);
    lean_dec_ref(v_inst_4292_);
    return v_res_4297_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(
    mut v_x_4298_: *mut LeanObject,
    mut v_x_4299_: *mut LeanObject,
    mut v_h__1_4300_: *mut LeanObject,
    mut v_h__2_4301_: *mut LeanObject,
    mut v_h__3_4302_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4298_) == 0 {
        let mut v_l_4303_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4300_);
        v_l_4303_ = lean_ctor_get(v_x_4298_, 3);
        if lean_obj_tag(v_l_4303_) == 0 {
            let mut v_size_4304_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4305_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4306_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4307_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4308_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4309_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4310_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4311_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4312_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4303_);
            lean_dec(v_h__2_4301_);
            v_size_4304_ = lean_ctor_get(v_x_4298_, 0);
            lean_inc(v_size_4304_);
            v_k_4305_ = lean_ctor_get(v_x_4298_, 1);
            lean_inc(v_k_4305_);
            v_v_4306_ = lean_ctor_get(v_x_4298_, 2);
            lean_inc(v_v_4306_);
            v_r_4307_ = lean_ctor_get(v_x_4298_, 4);
            lean_inc(v_r_4307_);
            lean_dec_ref_known(v_x_4298_, 5);
            v_size_4308_ = lean_ctor_get(v_l_4303_, 0);
            lean_inc(v_size_4308_);
            v_k_4309_ = lean_ctor_get(v_l_4303_, 1);
            lean_inc(v_k_4309_);
            v_v_4310_ = lean_ctor_get(v_l_4303_, 2);
            lean_inc(v_v_4310_);
            v_l_4311_ = lean_ctor_get(v_l_4303_, 3);
            lean_inc(v_l_4311_);
            v_r_4312_ = lean_ctor_get(v_l_4303_, 4);
            lean_inc(v_r_4312_);
            lean_dec_ref_known(v_l_4303_, 5);
            v___x_4313_ = lean_apply_10(
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
            let mut v_size_4314_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4315_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4316_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4302_);
            v_size_4314_ = lean_ctor_get(v_x_4298_, 0);
            lean_inc(v_size_4314_);
            v_k_4315_ = lean_ctor_get(v_x_4298_, 1);
            lean_inc(v_k_4315_);
            v_v_4316_ = lean_ctor_get(v_x_4298_, 2);
            lean_inc(v_v_4316_);
            v_r_4317_ = lean_ctor_get(v_x_4298_, 4);
            lean_inc(v_r_4317_);
            lean_dec_ref_known(v_x_4298_, 5);
            v___x_4318_ = lean_apply_5(
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
        let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4302_);
        lean_dec(v_h__2_4301_);
        v___x_4319_ = lean_apply_1(v_h__1_4300_, v_x_4299_);
        return v___x_4319_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(
    mut v_00_u03b1_4320_: *mut LeanObject,
    mut v_00_u03b2_4321_: *mut LeanObject,
    mut v_motive_4322_: *mut LeanObject,
    mut v_x_4323_: *mut LeanObject,
    mut v_x_4324_: *mut LeanObject,
    mut v_h__1_4325_: *mut LeanObject,
    mut v_h__2_4326_: *mut LeanObject,
    mut v_h__3_4327_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4323_) == 0 {
        let mut v_l_4328_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4325_);
        v_l_4328_ = lean_ctor_get(v_x_4323_, 3);
        if lean_obj_tag(v_l_4328_) == 0 {
            let mut v_size_4329_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4330_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4331_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4332_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4333_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4334_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4335_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4336_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4337_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4328_);
            lean_dec(v_h__2_4326_);
            v_size_4329_ = lean_ctor_get(v_x_4323_, 0);
            lean_inc(v_size_4329_);
            v_k_4330_ = lean_ctor_get(v_x_4323_, 1);
            lean_inc(v_k_4330_);
            v_v_4331_ = lean_ctor_get(v_x_4323_, 2);
            lean_inc(v_v_4331_);
            v_r_4332_ = lean_ctor_get(v_x_4323_, 4);
            lean_inc(v_r_4332_);
            lean_dec_ref_known(v_x_4323_, 5);
            v_size_4333_ = lean_ctor_get(v_l_4328_, 0);
            lean_inc(v_size_4333_);
            v_k_4334_ = lean_ctor_get(v_l_4328_, 1);
            lean_inc(v_k_4334_);
            v_v_4335_ = lean_ctor_get(v_l_4328_, 2);
            lean_inc(v_v_4335_);
            v_l_4336_ = lean_ctor_get(v_l_4328_, 3);
            lean_inc(v_l_4336_);
            v_r_4337_ = lean_ctor_get(v_l_4328_, 4);
            lean_inc(v_r_4337_);
            lean_dec_ref_known(v_l_4328_, 5);
            v___x_4338_ = lean_apply_10(
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
            let mut v_size_4339_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4340_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4341_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4327_);
            v_size_4339_ = lean_ctor_get(v_x_4323_, 0);
            lean_inc(v_size_4339_);
            v_k_4340_ = lean_ctor_get(v_x_4323_, 1);
            lean_inc(v_k_4340_);
            v_v_4341_ = lean_ctor_get(v_x_4323_, 2);
            lean_inc(v_v_4341_);
            v_r_4342_ = lean_ctor_get(v_x_4323_, 4);
            lean_inc(v_r_4342_);
            lean_dec_ref_known(v_x_4323_, 5);
            v___x_4343_ = lean_apply_5(
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
        let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4327_);
        lean_dec(v_h__2_4326_);
        v___x_4344_ = lean_apply_1(v_h__1_4325_, v_x_4324_);
        return v___x_4344_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(
    mut v_x_4345_: *mut LeanObject,
    mut v_h__1_4346_: *mut LeanObject,
    mut v_h__2_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_l_4348_: *mut LeanObject = core::ptr::null_mut();
    v_l_4348_ = lean_ctor_get(v_x_4345_, 3);
    if lean_obj_tag(v_l_4348_) == 0 {
        let mut v_size_4349_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4350_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4351_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4352_: *mut LeanObject = core::ptr::null_mut();
        let mut v_size_4353_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4354_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4355_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4356_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_l_4348_);
        lean_dec(v_h__1_4346_);
        v_size_4349_ = lean_ctor_get(v_x_4345_, 0);
        lean_inc(v_size_4349_);
        v_k_4350_ = lean_ctor_get(v_x_4345_, 1);
        lean_inc(v_k_4350_);
        v_v_4351_ = lean_ctor_get(v_x_4345_, 2);
        lean_inc(v_v_4351_);
        v_r_4352_ = lean_ctor_get(v_x_4345_, 4);
        lean_inc(v_r_4352_);
        lean_dec(v_x_4345_);
        v_size_4353_ = lean_ctor_get(v_l_4348_, 0);
        lean_inc(v_size_4353_);
        v_k_4354_ = lean_ctor_get(v_l_4348_, 1);
        lean_inc(v_k_4354_);
        v_v_4355_ = lean_ctor_get(v_l_4348_, 2);
        lean_inc(v_v_4355_);
        v_l_4356_ = lean_ctor_get(v_l_4348_, 3);
        lean_inc(v_l_4356_);
        v_r_4357_ = lean_ctor_get(v_l_4348_, 4);
        lean_inc(v_r_4357_);
        lean_dec_ref_known(v_l_4348_, 5);
        v___x_4358_ = lean_apply_10(
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
            lean_box(0),
        );
        return v___x_4358_;
    } else {
        let mut v_size_4359_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4360_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4361_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4347_);
        v_size_4359_ = lean_ctor_get(v_x_4345_, 0);
        lean_inc(v_size_4359_);
        v_k_4360_ = lean_ctor_get(v_x_4345_, 1);
        lean_inc(v_k_4360_);
        v_v_4361_ = lean_ctor_get(v_x_4345_, 2);
        lean_inc(v_v_4361_);
        v_r_4362_ = lean_ctor_get(v_x_4345_, 4);
        lean_inc(v_r_4362_);
        lean_dec(v_x_4345_);
        v___x_4363_ = lean_apply_5(
            v_h__1_4346_,
            v_size_4359_,
            v_k_4360_,
            v_v_4361_,
            v_r_4362_,
            lean_box(0),
        );
        return v___x_4363_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(
    mut v_00_u03b1_4364_: *mut LeanObject,
    mut v_00_u03b2_4365_: *mut LeanObject,
    mut v_motive_4366_: *mut LeanObject,
    mut v_x_4367_: *mut LeanObject,
    mut v_x_4368_: *mut LeanObject,
    mut v_h__1_4369_: *mut LeanObject,
    mut v_h__2_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_l_4371_: *mut LeanObject = core::ptr::null_mut();
    v_l_4371_ = lean_ctor_get(v_x_4367_, 3);
    if lean_obj_tag(v_l_4371_) == 0 {
        let mut v_size_4372_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4373_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4374_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4375_: *mut LeanObject = core::ptr::null_mut();
        let mut v_size_4376_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4377_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4378_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4379_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_l_4371_);
        lean_dec(v_h__1_4369_);
        v_size_4372_ = lean_ctor_get(v_x_4367_, 0);
        lean_inc(v_size_4372_);
        v_k_4373_ = lean_ctor_get(v_x_4367_, 1);
        lean_inc(v_k_4373_);
        v_v_4374_ = lean_ctor_get(v_x_4367_, 2);
        lean_inc(v_v_4374_);
        v_r_4375_ = lean_ctor_get(v_x_4367_, 4);
        lean_inc(v_r_4375_);
        lean_dec(v_x_4367_);
        v_size_4376_ = lean_ctor_get(v_l_4371_, 0);
        lean_inc(v_size_4376_);
        v_k_4377_ = lean_ctor_get(v_l_4371_, 1);
        lean_inc(v_k_4377_);
        v_v_4378_ = lean_ctor_get(v_l_4371_, 2);
        lean_inc(v_v_4378_);
        v_l_4379_ = lean_ctor_get(v_l_4371_, 3);
        lean_inc(v_l_4379_);
        v_r_4380_ = lean_ctor_get(v_l_4371_, 4);
        lean_inc(v_r_4380_);
        lean_dec_ref_known(v_l_4371_, 5);
        v___x_4381_ = lean_apply_10(
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
            lean_box(0),
        );
        return v___x_4381_;
    } else {
        let mut v_size_4382_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4383_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4384_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4370_);
        v_size_4382_ = lean_ctor_get(v_x_4367_, 0);
        lean_inc(v_size_4382_);
        v_k_4383_ = lean_ctor_get(v_x_4367_, 1);
        lean_inc(v_k_4383_);
        v_v_4384_ = lean_ctor_get(v_x_4367_, 2);
        lean_inc(v_v_4384_);
        v_r_4385_ = lean_ctor_get(v_x_4367_, 4);
        lean_inc(v_r_4385_);
        lean_dec(v_x_4367_);
        v___x_4386_ = lean_apply_5(
            v_h__1_4369_,
            v_size_4382_,
            v_k_4383_,
            v_v_4384_,
            v_r_4385_,
            lean_box(0),
        );
        return v___x_4386_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(
    mut v_x_4387_: *mut LeanObject,
    mut v_h__1_4388_: *mut LeanObject,
    mut v_h__2_4389_: *mut LeanObject,
    mut v_h__3_4390_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4387_) == 0 {
        let mut v_r_4391_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4388_);
        v_r_4391_ = lean_ctor_get(v_x_4387_, 4);
        if lean_obj_tag(v_r_4391_) == 0 {
            let mut v_size_4392_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4393_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4394_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4395_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4396_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4397_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4398_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4399_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4400_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4391_);
            lean_dec(v_h__2_4389_);
            v_size_4392_ = lean_ctor_get(v_x_4387_, 0);
            lean_inc(v_size_4392_);
            v_k_4393_ = lean_ctor_get(v_x_4387_, 1);
            lean_inc(v_k_4393_);
            v_v_4394_ = lean_ctor_get(v_x_4387_, 2);
            lean_inc(v_v_4394_);
            v_l_4395_ = lean_ctor_get(v_x_4387_, 3);
            lean_inc(v_l_4395_);
            lean_dec_ref_known(v_x_4387_, 5);
            v_size_4396_ = lean_ctor_get(v_r_4391_, 0);
            lean_inc(v_size_4396_);
            v_k_4397_ = lean_ctor_get(v_r_4391_, 1);
            lean_inc(v_k_4397_);
            v_v_4398_ = lean_ctor_get(v_r_4391_, 2);
            lean_inc(v_v_4398_);
            v_l_4399_ = lean_ctor_get(v_r_4391_, 3);
            lean_inc(v_l_4399_);
            v_r_4400_ = lean_ctor_get(v_r_4391_, 4);
            lean_inc(v_r_4400_);
            lean_dec_ref_known(v_r_4391_, 5);
            v___x_4401_ = lean_apply_9(
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
            let mut v_size_4402_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4403_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4404_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4405_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4390_);
            v_size_4402_ = lean_ctor_get(v_x_4387_, 0);
            lean_inc(v_size_4402_);
            v_k_4403_ = lean_ctor_get(v_x_4387_, 1);
            lean_inc(v_k_4403_);
            v_v_4404_ = lean_ctor_get(v_x_4387_, 2);
            lean_inc(v_v_4404_);
            v_l_4405_ = lean_ctor_get(v_x_4387_, 3);
            lean_inc(v_l_4405_);
            lean_dec_ref_known(v_x_4387_, 5);
            v___x_4406_ = lean_apply_4(v_h__2_4389_, v_size_4402_, v_k_4403_, v_v_4404_, v_l_4405_);
            return v___x_4406_;
        }
    } else {
        let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4390_);
        lean_dec(v_h__2_4389_);
        v___x_4407_ = lean_box(0);
        v___x_4408_ = lean_apply_1(v_h__1_4388_, v___x_4407_);
        return v___x_4408_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4409_: *mut LeanObject,
    mut v_00_u03b2_4410_: *mut LeanObject,
    mut v_motive_4411_: *mut LeanObject,
    mut v_x_4412_: *mut LeanObject,
    mut v_h__1_4413_: *mut LeanObject,
    mut v_h__2_4414_: *mut LeanObject,
    mut v_h__3_4415_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4412_) == 0 {
        let mut v_r_4416_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4413_);
        v_r_4416_ = lean_ctor_get(v_x_4412_, 4);
        if lean_obj_tag(v_r_4416_) == 0 {
            let mut v_size_4417_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4418_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4419_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4420_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4421_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4422_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4423_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4424_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4425_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4416_);
            lean_dec(v_h__2_4414_);
            v_size_4417_ = lean_ctor_get(v_x_4412_, 0);
            lean_inc(v_size_4417_);
            v_k_4418_ = lean_ctor_get(v_x_4412_, 1);
            lean_inc(v_k_4418_);
            v_v_4419_ = lean_ctor_get(v_x_4412_, 2);
            lean_inc(v_v_4419_);
            v_l_4420_ = lean_ctor_get(v_x_4412_, 3);
            lean_inc(v_l_4420_);
            lean_dec_ref_known(v_x_4412_, 5);
            v_size_4421_ = lean_ctor_get(v_r_4416_, 0);
            lean_inc(v_size_4421_);
            v_k_4422_ = lean_ctor_get(v_r_4416_, 1);
            lean_inc(v_k_4422_);
            v_v_4423_ = lean_ctor_get(v_r_4416_, 2);
            lean_inc(v_v_4423_);
            v_l_4424_ = lean_ctor_get(v_r_4416_, 3);
            lean_inc(v_l_4424_);
            v_r_4425_ = lean_ctor_get(v_r_4416_, 4);
            lean_inc(v_r_4425_);
            lean_dec_ref_known(v_r_4416_, 5);
            v___x_4426_ = lean_apply_9(
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
            let mut v_size_4427_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4428_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4429_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4430_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4415_);
            v_size_4427_ = lean_ctor_get(v_x_4412_, 0);
            lean_inc(v_size_4427_);
            v_k_4428_ = lean_ctor_get(v_x_4412_, 1);
            lean_inc(v_k_4428_);
            v_v_4429_ = lean_ctor_get(v_x_4412_, 2);
            lean_inc(v_v_4429_);
            v_l_4430_ = lean_ctor_get(v_x_4412_, 3);
            lean_inc(v_l_4430_);
            lean_dec_ref_known(v_x_4412_, 5);
            v___x_4431_ = lean_apply_4(v_h__2_4414_, v_size_4427_, v_k_4428_, v_v_4429_, v_l_4430_);
            return v___x_4431_;
        }
    } else {
        let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4415_);
        lean_dec(v_h__2_4414_);
        v___x_4432_ = lean_box(0);
        v___x_4433_ = lean_apply_1(v_h__1_4413_, v___x_4432_);
        return v___x_4433_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(
    mut v_x_4434_: *mut LeanObject,
    mut v_x_4435_: *mut LeanObject,
    mut v_h__1_4436_: *mut LeanObject,
    mut v_h__2_4437_: *mut LeanObject,
    mut v_h__3_4438_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4434_) == 0 {
        let mut v_r_4439_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4436_);
        v_r_4439_ = lean_ctor_get(v_x_4434_, 4);
        if lean_obj_tag(v_r_4439_) == 0 {
            let mut v_size_4440_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4441_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4442_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4443_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4444_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4445_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4446_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4447_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4448_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4439_);
            lean_dec(v_h__2_4437_);
            v_size_4440_ = lean_ctor_get(v_x_4434_, 0);
            lean_inc(v_size_4440_);
            v_k_4441_ = lean_ctor_get(v_x_4434_, 1);
            lean_inc(v_k_4441_);
            v_v_4442_ = lean_ctor_get(v_x_4434_, 2);
            lean_inc(v_v_4442_);
            v_l_4443_ = lean_ctor_get(v_x_4434_, 3);
            lean_inc(v_l_4443_);
            lean_dec_ref_known(v_x_4434_, 5);
            v_size_4444_ = lean_ctor_get(v_r_4439_, 0);
            lean_inc(v_size_4444_);
            v_k_4445_ = lean_ctor_get(v_r_4439_, 1);
            lean_inc(v_k_4445_);
            v_v_4446_ = lean_ctor_get(v_r_4439_, 2);
            lean_inc(v_v_4446_);
            v_l_4447_ = lean_ctor_get(v_r_4439_, 3);
            lean_inc(v_l_4447_);
            v_r_4448_ = lean_ctor_get(v_r_4439_, 4);
            lean_inc(v_r_4448_);
            lean_dec_ref_known(v_r_4439_, 5);
            v___x_4449_ = lean_apply_10(
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
            let mut v_size_4450_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4451_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4452_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4453_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4438_);
            v_size_4450_ = lean_ctor_get(v_x_4434_, 0);
            lean_inc(v_size_4450_);
            v_k_4451_ = lean_ctor_get(v_x_4434_, 1);
            lean_inc(v_k_4451_);
            v_v_4452_ = lean_ctor_get(v_x_4434_, 2);
            lean_inc(v_v_4452_);
            v_l_4453_ = lean_ctor_get(v_x_4434_, 3);
            lean_inc(v_l_4453_);
            lean_dec_ref_known(v_x_4434_, 5);
            v___x_4454_ = lean_apply_5(
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
        let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4438_);
        lean_dec(v_h__2_4437_);
        v___x_4455_ = lean_apply_1(v_h__1_4436_, v_x_4435_);
        return v___x_4455_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(
    mut v_00_u03b1_4456_: *mut LeanObject,
    mut v_00_u03b2_4457_: *mut LeanObject,
    mut v_motive_4458_: *mut LeanObject,
    mut v_x_4459_: *mut LeanObject,
    mut v_x_4460_: *mut LeanObject,
    mut v_h__1_4461_: *mut LeanObject,
    mut v_h__2_4462_: *mut LeanObject,
    mut v_h__3_4463_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4459_) == 0 {
        let mut v_r_4464_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4461_);
        v_r_4464_ = lean_ctor_get(v_x_4459_, 4);
        if lean_obj_tag(v_r_4464_) == 0 {
            let mut v_size_4465_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4466_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4467_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4468_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4469_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4470_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4471_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4472_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4473_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4464_);
            lean_dec(v_h__2_4462_);
            v_size_4465_ = lean_ctor_get(v_x_4459_, 0);
            lean_inc(v_size_4465_);
            v_k_4466_ = lean_ctor_get(v_x_4459_, 1);
            lean_inc(v_k_4466_);
            v_v_4467_ = lean_ctor_get(v_x_4459_, 2);
            lean_inc(v_v_4467_);
            v_l_4468_ = lean_ctor_get(v_x_4459_, 3);
            lean_inc(v_l_4468_);
            lean_dec_ref_known(v_x_4459_, 5);
            v_size_4469_ = lean_ctor_get(v_r_4464_, 0);
            lean_inc(v_size_4469_);
            v_k_4470_ = lean_ctor_get(v_r_4464_, 1);
            lean_inc(v_k_4470_);
            v_v_4471_ = lean_ctor_get(v_r_4464_, 2);
            lean_inc(v_v_4471_);
            v_l_4472_ = lean_ctor_get(v_r_4464_, 3);
            lean_inc(v_l_4472_);
            v_r_4473_ = lean_ctor_get(v_r_4464_, 4);
            lean_inc(v_r_4473_);
            lean_dec_ref_known(v_r_4464_, 5);
            v___x_4474_ = lean_apply_10(
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
            let mut v_size_4475_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4476_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4477_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4478_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4463_);
            v_size_4475_ = lean_ctor_get(v_x_4459_, 0);
            lean_inc(v_size_4475_);
            v_k_4476_ = lean_ctor_get(v_x_4459_, 1);
            lean_inc(v_k_4476_);
            v_v_4477_ = lean_ctor_get(v_x_4459_, 2);
            lean_inc(v_v_4477_);
            v_l_4478_ = lean_ctor_get(v_x_4459_, 3);
            lean_inc(v_l_4478_);
            lean_dec_ref_known(v_x_4459_, 5);
            v___x_4479_ = lean_apply_5(
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
        let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4463_);
        lean_dec(v_h__2_4462_);
        v___x_4480_ = lean_apply_1(v_h__1_4461_, v_x_4460_);
        return v___x_4480_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(
    mut v_x_4481_: *mut LeanObject,
    mut v_h__1_4482_: *mut LeanObject,
    mut v_h__2_4483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_4484_: *mut LeanObject = core::ptr::null_mut();
    v_r_4484_ = lean_ctor_get(v_x_4481_, 4);
    if lean_obj_tag(v_r_4484_) == 0 {
        let mut v_size_4485_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4486_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4487_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4488_: *mut LeanObject = core::ptr::null_mut();
        let mut v_size_4489_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4490_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4491_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4492_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_r_4484_);
        lean_dec(v_h__1_4482_);
        v_size_4485_ = lean_ctor_get(v_x_4481_, 0);
        lean_inc(v_size_4485_);
        v_k_4486_ = lean_ctor_get(v_x_4481_, 1);
        lean_inc(v_k_4486_);
        v_v_4487_ = lean_ctor_get(v_x_4481_, 2);
        lean_inc(v_v_4487_);
        v_l_4488_ = lean_ctor_get(v_x_4481_, 3);
        lean_inc(v_l_4488_);
        lean_dec(v_x_4481_);
        v_size_4489_ = lean_ctor_get(v_r_4484_, 0);
        lean_inc(v_size_4489_);
        v_k_4490_ = lean_ctor_get(v_r_4484_, 1);
        lean_inc(v_k_4490_);
        v_v_4491_ = lean_ctor_get(v_r_4484_, 2);
        lean_inc(v_v_4491_);
        v_l_4492_ = lean_ctor_get(v_r_4484_, 3);
        lean_inc(v_l_4492_);
        v_r_4493_ = lean_ctor_get(v_r_4484_, 4);
        lean_inc(v_r_4493_);
        lean_dec_ref_known(v_r_4484_, 5);
        v___x_4494_ = lean_apply_10(
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
            lean_box(0),
        );
        return v___x_4494_;
    } else {
        let mut v_size_4495_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4496_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4497_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4483_);
        v_size_4495_ = lean_ctor_get(v_x_4481_, 0);
        lean_inc(v_size_4495_);
        v_k_4496_ = lean_ctor_get(v_x_4481_, 1);
        lean_inc(v_k_4496_);
        v_v_4497_ = lean_ctor_get(v_x_4481_, 2);
        lean_inc(v_v_4497_);
        v_l_4498_ = lean_ctor_get(v_x_4481_, 3);
        lean_inc(v_l_4498_);
        lean_dec(v_x_4481_);
        v___x_4499_ = lean_apply_5(
            v_h__1_4482_,
            v_size_4495_,
            v_k_4496_,
            v_v_4497_,
            v_l_4498_,
            lean_box(0),
        );
        return v___x_4499_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(
    mut v_00_u03b1_4500_: *mut LeanObject,
    mut v_00_u03b2_4501_: *mut LeanObject,
    mut v_motive_4502_: *mut LeanObject,
    mut v_x_4503_: *mut LeanObject,
    mut v_x_4504_: *mut LeanObject,
    mut v_h__1_4505_: *mut LeanObject,
    mut v_h__2_4506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_4507_: *mut LeanObject = core::ptr::null_mut();
    v_r_4507_ = lean_ctor_get(v_x_4503_, 4);
    if lean_obj_tag(v_r_4507_) == 0 {
        let mut v_size_4508_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4509_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4510_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4511_: *mut LeanObject = core::ptr::null_mut();
        let mut v_size_4512_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4513_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4514_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4515_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_r_4507_);
        lean_dec(v_h__1_4505_);
        v_size_4508_ = lean_ctor_get(v_x_4503_, 0);
        lean_inc(v_size_4508_);
        v_k_4509_ = lean_ctor_get(v_x_4503_, 1);
        lean_inc(v_k_4509_);
        v_v_4510_ = lean_ctor_get(v_x_4503_, 2);
        lean_inc(v_v_4510_);
        v_l_4511_ = lean_ctor_get(v_x_4503_, 3);
        lean_inc(v_l_4511_);
        lean_dec(v_x_4503_);
        v_size_4512_ = lean_ctor_get(v_r_4507_, 0);
        lean_inc(v_size_4512_);
        v_k_4513_ = lean_ctor_get(v_r_4507_, 1);
        lean_inc(v_k_4513_);
        v_v_4514_ = lean_ctor_get(v_r_4507_, 2);
        lean_inc(v_v_4514_);
        v_l_4515_ = lean_ctor_get(v_r_4507_, 3);
        lean_inc(v_l_4515_);
        v_r_4516_ = lean_ctor_get(v_r_4507_, 4);
        lean_inc(v_r_4516_);
        lean_dec_ref_known(v_r_4507_, 5);
        v___x_4517_ = lean_apply_10(
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
            lean_box(0),
        );
        return v___x_4517_;
    } else {
        let mut v_size_4518_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4519_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4520_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4506_);
        v_size_4518_ = lean_ctor_get(v_x_4503_, 0);
        lean_inc(v_size_4518_);
        v_k_4519_ = lean_ctor_get(v_x_4503_, 1);
        lean_inc(v_k_4519_);
        v_v_4520_ = lean_ctor_get(v_x_4503_, 2);
        lean_inc(v_v_4520_);
        v_l_4521_ = lean_ctor_get(v_x_4503_, 3);
        lean_inc(v_l_4521_);
        lean_dec(v_x_4503_);
        v___x_4522_ = lean_apply_5(
            v_h__1_4505_,
            v_size_4518_,
            v_k_4519_,
            v_v_4520_,
            v_l_4521_,
            lean_box(0),
        );
        return v___x_4522_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(
    mut v_x_4523_: *mut LeanObject,
    mut v_x_4524_: *mut LeanObject,
    mut v_h__1_4525_: *mut LeanObject,
    mut v_h__2_4526_: *mut LeanObject,
    mut v_h__3_4527_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4523_) == 0 {
        let mut v_l_4528_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4525_);
        v_l_4528_ = lean_ctor_get(v_x_4523_, 3);
        if lean_obj_tag(v_l_4528_) == 0 {
            let mut v_size_4529_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4530_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4531_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4532_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4533_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4534_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4535_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4536_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4537_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4528_);
            lean_dec(v_h__2_4526_);
            v_size_4529_ = lean_ctor_get(v_x_4523_, 0);
            lean_inc(v_size_4529_);
            v_k_4530_ = lean_ctor_get(v_x_4523_, 1);
            lean_inc(v_k_4530_);
            v_v_4531_ = lean_ctor_get(v_x_4523_, 2);
            lean_inc(v_v_4531_);
            v_r_4532_ = lean_ctor_get(v_x_4523_, 4);
            lean_inc(v_r_4532_);
            lean_dec_ref_known(v_x_4523_, 5);
            v_size_4533_ = lean_ctor_get(v_l_4528_, 0);
            lean_inc(v_size_4533_);
            v_k_4534_ = lean_ctor_get(v_l_4528_, 1);
            lean_inc(v_k_4534_);
            v_v_4535_ = lean_ctor_get(v_l_4528_, 2);
            lean_inc(v_v_4535_);
            v_l_4536_ = lean_ctor_get(v_l_4528_, 3);
            lean_inc(v_l_4536_);
            v_r_4537_ = lean_ctor_get(v_l_4528_, 4);
            lean_inc(v_r_4537_);
            lean_dec_ref_known(v_l_4528_, 5);
            v___x_4538_ = lean_apply_10(
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
            let mut v_size_4539_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4540_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4541_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4542_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4527_);
            v_size_4539_ = lean_ctor_get(v_x_4523_, 0);
            lean_inc(v_size_4539_);
            v_k_4540_ = lean_ctor_get(v_x_4523_, 1);
            lean_inc(v_k_4540_);
            v_v_4541_ = lean_ctor_get(v_x_4523_, 2);
            lean_inc(v_v_4541_);
            v_r_4542_ = lean_ctor_get(v_x_4523_, 4);
            lean_inc(v_r_4542_);
            lean_dec_ref_known(v_x_4523_, 5);
            v___x_4543_ = lean_apply_5(
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
        let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4527_);
        lean_dec(v_h__2_4526_);
        v___x_4544_ = lean_apply_1(v_h__1_4525_, v_x_4524_);
        return v___x_4544_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(
    mut v_00_u03b1_4545_: *mut LeanObject,
    mut v_00_u03b2_4546_: *mut LeanObject,
    mut v_motive_4547_: *mut LeanObject,
    mut v_x_4548_: *mut LeanObject,
    mut v_x_4549_: *mut LeanObject,
    mut v_h__1_4550_: *mut LeanObject,
    mut v_h__2_4551_: *mut LeanObject,
    mut v_h__3_4552_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4548_) == 0 {
        let mut v_l_4553_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4550_);
        v_l_4553_ = lean_ctor_get(v_x_4548_, 3);
        if lean_obj_tag(v_l_4553_) == 0 {
            let mut v_size_4554_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4555_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4556_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4557_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4558_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4559_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4560_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4561_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4562_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4553_);
            lean_dec(v_h__2_4551_);
            v_size_4554_ = lean_ctor_get(v_x_4548_, 0);
            lean_inc(v_size_4554_);
            v_k_4555_ = lean_ctor_get(v_x_4548_, 1);
            lean_inc(v_k_4555_);
            v_v_4556_ = lean_ctor_get(v_x_4548_, 2);
            lean_inc(v_v_4556_);
            v_r_4557_ = lean_ctor_get(v_x_4548_, 4);
            lean_inc(v_r_4557_);
            lean_dec_ref_known(v_x_4548_, 5);
            v_size_4558_ = lean_ctor_get(v_l_4553_, 0);
            lean_inc(v_size_4558_);
            v_k_4559_ = lean_ctor_get(v_l_4553_, 1);
            lean_inc(v_k_4559_);
            v_v_4560_ = lean_ctor_get(v_l_4553_, 2);
            lean_inc(v_v_4560_);
            v_l_4561_ = lean_ctor_get(v_l_4553_, 3);
            lean_inc(v_l_4561_);
            v_r_4562_ = lean_ctor_get(v_l_4553_, 4);
            lean_inc(v_r_4562_);
            lean_dec_ref_known(v_l_4553_, 5);
            v___x_4563_ = lean_apply_10(
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
            let mut v_size_4564_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4565_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4566_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4567_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4552_);
            v_size_4564_ = lean_ctor_get(v_x_4548_, 0);
            lean_inc(v_size_4564_);
            v_k_4565_ = lean_ctor_get(v_x_4548_, 1);
            lean_inc(v_k_4565_);
            v_v_4566_ = lean_ctor_get(v_x_4548_, 2);
            lean_inc(v_v_4566_);
            v_r_4567_ = lean_ctor_get(v_x_4548_, 4);
            lean_inc(v_r_4567_);
            lean_dec_ref_known(v_x_4548_, 5);
            v___x_4568_ = lean_apply_5(
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
        let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4552_);
        lean_dec(v_h__2_4551_);
        v___x_4569_ = lean_apply_1(v_h__1_4550_, v_x_4549_);
        return v___x_4569_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(
    mut v_x_4570_: *mut LeanObject,
    mut v_x_4571_: *mut LeanObject,
    mut v_h__1_4572_: *mut LeanObject,
    mut v_h__2_4573_: *mut LeanObject,
    mut v_h__3_4574_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4570_) == 0 {
        let mut v_r_4575_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4572_);
        v_r_4575_ = lean_ctor_get(v_x_4570_, 4);
        if lean_obj_tag(v_r_4575_) == 0 {
            let mut v_size_4576_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4577_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4578_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4579_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4580_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4581_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4582_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4583_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4584_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4575_);
            lean_dec(v_h__2_4573_);
            v_size_4576_ = lean_ctor_get(v_x_4570_, 0);
            lean_inc(v_size_4576_);
            v_k_4577_ = lean_ctor_get(v_x_4570_, 1);
            lean_inc(v_k_4577_);
            v_v_4578_ = lean_ctor_get(v_x_4570_, 2);
            lean_inc(v_v_4578_);
            v_l_4579_ = lean_ctor_get(v_x_4570_, 3);
            lean_inc(v_l_4579_);
            lean_dec_ref_known(v_x_4570_, 5);
            v_size_4580_ = lean_ctor_get(v_r_4575_, 0);
            lean_inc(v_size_4580_);
            v_k_4581_ = lean_ctor_get(v_r_4575_, 1);
            lean_inc(v_k_4581_);
            v_v_4582_ = lean_ctor_get(v_r_4575_, 2);
            lean_inc(v_v_4582_);
            v_l_4583_ = lean_ctor_get(v_r_4575_, 3);
            lean_inc(v_l_4583_);
            v_r_4584_ = lean_ctor_get(v_r_4575_, 4);
            lean_inc(v_r_4584_);
            lean_dec_ref_known(v_r_4575_, 5);
            v___x_4585_ = lean_apply_10(
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
            let mut v_size_4586_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4587_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4588_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4589_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4574_);
            v_size_4586_ = lean_ctor_get(v_x_4570_, 0);
            lean_inc(v_size_4586_);
            v_k_4587_ = lean_ctor_get(v_x_4570_, 1);
            lean_inc(v_k_4587_);
            v_v_4588_ = lean_ctor_get(v_x_4570_, 2);
            lean_inc(v_v_4588_);
            v_l_4589_ = lean_ctor_get(v_x_4570_, 3);
            lean_inc(v_l_4589_);
            lean_dec_ref_known(v_x_4570_, 5);
            v___x_4590_ = lean_apply_5(
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
        let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4574_);
        lean_dec(v_h__2_4573_);
        v___x_4591_ = lean_apply_1(v_h__1_4572_, v_x_4571_);
        return v___x_4591_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(
    mut v_00_u03b1_4592_: *mut LeanObject,
    mut v_00_u03b2_4593_: *mut LeanObject,
    mut v_motive_4594_: *mut LeanObject,
    mut v_x_4595_: *mut LeanObject,
    mut v_x_4596_: *mut LeanObject,
    mut v_h__1_4597_: *mut LeanObject,
    mut v_h__2_4598_: *mut LeanObject,
    mut v_h__3_4599_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4595_) == 0 {
        let mut v_r_4600_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4597_);
        v_r_4600_ = lean_ctor_get(v_x_4595_, 4);
        if lean_obj_tag(v_r_4600_) == 0 {
            let mut v_size_4601_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4602_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4603_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4604_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4605_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4606_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4607_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4608_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4609_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4600_);
            lean_dec(v_h__2_4598_);
            v_size_4601_ = lean_ctor_get(v_x_4595_, 0);
            lean_inc(v_size_4601_);
            v_k_4602_ = lean_ctor_get(v_x_4595_, 1);
            lean_inc(v_k_4602_);
            v_v_4603_ = lean_ctor_get(v_x_4595_, 2);
            lean_inc(v_v_4603_);
            v_l_4604_ = lean_ctor_get(v_x_4595_, 3);
            lean_inc(v_l_4604_);
            lean_dec_ref_known(v_x_4595_, 5);
            v_size_4605_ = lean_ctor_get(v_r_4600_, 0);
            lean_inc(v_size_4605_);
            v_k_4606_ = lean_ctor_get(v_r_4600_, 1);
            lean_inc(v_k_4606_);
            v_v_4607_ = lean_ctor_get(v_r_4600_, 2);
            lean_inc(v_v_4607_);
            v_l_4608_ = lean_ctor_get(v_r_4600_, 3);
            lean_inc(v_l_4608_);
            v_r_4609_ = lean_ctor_get(v_r_4600_, 4);
            lean_inc(v_r_4609_);
            lean_dec_ref_known(v_r_4600_, 5);
            v___x_4610_ = lean_apply_10(
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
            let mut v_size_4611_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4612_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4613_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4614_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4599_);
            v_size_4611_ = lean_ctor_get(v_x_4595_, 0);
            lean_inc(v_size_4611_);
            v_k_4612_ = lean_ctor_get(v_x_4595_, 1);
            lean_inc(v_k_4612_);
            v_v_4613_ = lean_ctor_get(v_x_4595_, 2);
            lean_inc(v_v_4613_);
            v_l_4614_ = lean_ctor_get(v_x_4595_, 3);
            lean_inc(v_l_4614_);
            lean_dec_ref_known(v_x_4595_, 5);
            v___x_4615_ = lean_apply_5(
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
        let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4599_);
        lean_dec(v_h__2_4598_);
        v___x_4616_ = lean_apply_1(v_h__1_4597_, v_x_4596_);
        return v___x_4616_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(
    mut v_x_4617_: *mut LeanObject,
    mut v_h__1_4618_: *mut LeanObject,
    mut v_h__2_4619_: *mut LeanObject,
    mut v_h__3_4620_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4617_) == 0 {
        let mut v_l_4621_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4618_);
        v_l_4621_ = lean_ctor_get(v_x_4617_, 3);
        if lean_obj_tag(v_l_4621_) == 0 {
            let mut v_size_4622_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4623_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4624_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4625_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4626_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4627_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4628_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4629_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4630_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4621_);
            lean_dec(v_h__2_4619_);
            v_size_4622_ = lean_ctor_get(v_x_4617_, 0);
            lean_inc(v_size_4622_);
            v_k_4623_ = lean_ctor_get(v_x_4617_, 1);
            lean_inc(v_k_4623_);
            v_v_4624_ = lean_ctor_get(v_x_4617_, 2);
            lean_inc(v_v_4624_);
            v_r_4625_ = lean_ctor_get(v_x_4617_, 4);
            lean_inc(v_r_4625_);
            lean_dec_ref_known(v_x_4617_, 5);
            v_size_4626_ = lean_ctor_get(v_l_4621_, 0);
            lean_inc(v_size_4626_);
            v_k_4627_ = lean_ctor_get(v_l_4621_, 1);
            lean_inc(v_k_4627_);
            v_v_4628_ = lean_ctor_get(v_l_4621_, 2);
            lean_inc(v_v_4628_);
            v_l_4629_ = lean_ctor_get(v_l_4621_, 3);
            lean_inc(v_l_4629_);
            v_r_4630_ = lean_ctor_get(v_l_4621_, 4);
            lean_inc(v_r_4630_);
            lean_dec_ref_known(v_l_4621_, 5);
            v___x_4631_ = lean_apply_9(
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
            let mut v_size_4632_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4633_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4634_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4635_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4620_);
            v_size_4632_ = lean_ctor_get(v_x_4617_, 0);
            lean_inc(v_size_4632_);
            v_k_4633_ = lean_ctor_get(v_x_4617_, 1);
            lean_inc(v_k_4633_);
            v_v_4634_ = lean_ctor_get(v_x_4617_, 2);
            lean_inc(v_v_4634_);
            v_r_4635_ = lean_ctor_get(v_x_4617_, 4);
            lean_inc(v_r_4635_);
            lean_dec_ref_known(v_x_4617_, 5);
            v___x_4636_ = lean_apply_4(v_h__2_4619_, v_size_4632_, v_k_4633_, v_v_4634_, v_r_4635_);
            return v___x_4636_;
        }
    } else {
        let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4620_);
        lean_dec(v_h__2_4619_);
        v___x_4637_ = lean_box(0);
        v___x_4638_ = lean_apply_1(v_h__1_4618_, v___x_4637_);
        return v___x_4638_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4639_: *mut LeanObject,
    mut v_00_u03b2_4640_: *mut LeanObject,
    mut v_motive_4641_: *mut LeanObject,
    mut v_x_4642_: *mut LeanObject,
    mut v_h__1_4643_: *mut LeanObject,
    mut v_h__2_4644_: *mut LeanObject,
    mut v_h__3_4645_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4642_) == 0 {
        let mut v_l_4646_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4643_);
        v_l_4646_ = lean_ctor_get(v_x_4642_, 3);
        if lean_obj_tag(v_l_4646_) == 0 {
            let mut v_size_4647_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4648_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4649_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4650_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4651_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4652_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4653_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4654_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4655_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4646_);
            lean_dec(v_h__2_4644_);
            v_size_4647_ = lean_ctor_get(v_x_4642_, 0);
            lean_inc(v_size_4647_);
            v_k_4648_ = lean_ctor_get(v_x_4642_, 1);
            lean_inc(v_k_4648_);
            v_v_4649_ = lean_ctor_get(v_x_4642_, 2);
            lean_inc(v_v_4649_);
            v_r_4650_ = lean_ctor_get(v_x_4642_, 4);
            lean_inc(v_r_4650_);
            lean_dec_ref_known(v_x_4642_, 5);
            v_size_4651_ = lean_ctor_get(v_l_4646_, 0);
            lean_inc(v_size_4651_);
            v_k_4652_ = lean_ctor_get(v_l_4646_, 1);
            lean_inc(v_k_4652_);
            v_v_4653_ = lean_ctor_get(v_l_4646_, 2);
            lean_inc(v_v_4653_);
            v_l_4654_ = lean_ctor_get(v_l_4646_, 3);
            lean_inc(v_l_4654_);
            v_r_4655_ = lean_ctor_get(v_l_4646_, 4);
            lean_inc(v_r_4655_);
            lean_dec_ref_known(v_l_4646_, 5);
            v___x_4656_ = lean_apply_9(
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
            let mut v_size_4657_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4658_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4659_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4660_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4645_);
            v_size_4657_ = lean_ctor_get(v_x_4642_, 0);
            lean_inc(v_size_4657_);
            v_k_4658_ = lean_ctor_get(v_x_4642_, 1);
            lean_inc(v_k_4658_);
            v_v_4659_ = lean_ctor_get(v_x_4642_, 2);
            lean_inc(v_v_4659_);
            v_r_4660_ = lean_ctor_get(v_x_4642_, 4);
            lean_inc(v_r_4660_);
            lean_dec_ref_known(v_x_4642_, 5);
            v___x_4661_ = lean_apply_4(v_h__2_4644_, v_size_4657_, v_k_4658_, v_v_4659_, v_r_4660_);
            return v___x_4661_;
        }
    } else {
        let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4645_);
        lean_dec(v_h__2_4644_);
        v___x_4662_ = lean_box(0);
        v___x_4663_ = lean_apply_1(v_h__1_4643_, v___x_4662_);
        return v___x_4663_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(
    mut v_x_4664_: *mut LeanObject,
    mut v_x_4665_: *mut LeanObject,
    mut v_h__1_4666_: *mut LeanObject,
    mut v_h__2_4667_: *mut LeanObject,
    mut v_h__3_4668_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4664_) == 0 {
        let mut v_l_4669_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4666_);
        v_l_4669_ = lean_ctor_get(v_x_4664_, 3);
        if lean_obj_tag(v_l_4669_) == 0 {
            let mut v_size_4670_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4671_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4672_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4673_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4674_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4675_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4676_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4677_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4678_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4669_);
            lean_dec(v_h__2_4667_);
            v_size_4670_ = lean_ctor_get(v_x_4664_, 0);
            lean_inc(v_size_4670_);
            v_k_4671_ = lean_ctor_get(v_x_4664_, 1);
            lean_inc(v_k_4671_);
            v_v_4672_ = lean_ctor_get(v_x_4664_, 2);
            lean_inc(v_v_4672_);
            v_r_4673_ = lean_ctor_get(v_x_4664_, 4);
            lean_inc(v_r_4673_);
            lean_dec_ref_known(v_x_4664_, 5);
            v_size_4674_ = lean_ctor_get(v_l_4669_, 0);
            lean_inc(v_size_4674_);
            v_k_4675_ = lean_ctor_get(v_l_4669_, 1);
            lean_inc(v_k_4675_);
            v_v_4676_ = lean_ctor_get(v_l_4669_, 2);
            lean_inc(v_v_4676_);
            v_l_4677_ = lean_ctor_get(v_l_4669_, 3);
            lean_inc(v_l_4677_);
            v_r_4678_ = lean_ctor_get(v_l_4669_, 4);
            lean_inc(v_r_4678_);
            lean_dec_ref_known(v_l_4669_, 5);
            v___x_4679_ = lean_apply_10(
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
            let mut v_size_4680_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4681_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4682_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4683_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4668_);
            v_size_4680_ = lean_ctor_get(v_x_4664_, 0);
            lean_inc(v_size_4680_);
            v_k_4681_ = lean_ctor_get(v_x_4664_, 1);
            lean_inc(v_k_4681_);
            v_v_4682_ = lean_ctor_get(v_x_4664_, 2);
            lean_inc(v_v_4682_);
            v_r_4683_ = lean_ctor_get(v_x_4664_, 4);
            lean_inc(v_r_4683_);
            lean_dec_ref_known(v_x_4664_, 5);
            v___x_4684_ = lean_apply_5(
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
        let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4668_);
        lean_dec(v_h__2_4667_);
        v___x_4685_ = lean_apply_1(v_h__1_4666_, v_x_4665_);
        return v___x_4685_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(
    mut v_00_u03b1_4686_: *mut LeanObject,
    mut v_00_u03b2_4687_: *mut LeanObject,
    mut v_motive_4688_: *mut LeanObject,
    mut v_x_4689_: *mut LeanObject,
    mut v_x_4690_: *mut LeanObject,
    mut v_h__1_4691_: *mut LeanObject,
    mut v_h__2_4692_: *mut LeanObject,
    mut v_h__3_4693_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4689_) == 0 {
        let mut v_l_4694_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4691_);
        v_l_4694_ = lean_ctor_get(v_x_4689_, 3);
        if lean_obj_tag(v_l_4694_) == 0 {
            let mut v_size_4695_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4696_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4697_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4698_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4699_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4700_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4701_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4702_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4703_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_l_4694_);
            lean_dec(v_h__2_4692_);
            v_size_4695_ = lean_ctor_get(v_x_4689_, 0);
            lean_inc(v_size_4695_);
            v_k_4696_ = lean_ctor_get(v_x_4689_, 1);
            lean_inc(v_k_4696_);
            v_v_4697_ = lean_ctor_get(v_x_4689_, 2);
            lean_inc(v_v_4697_);
            v_r_4698_ = lean_ctor_get(v_x_4689_, 4);
            lean_inc(v_r_4698_);
            lean_dec_ref_known(v_x_4689_, 5);
            v_size_4699_ = lean_ctor_get(v_l_4694_, 0);
            lean_inc(v_size_4699_);
            v_k_4700_ = lean_ctor_get(v_l_4694_, 1);
            lean_inc(v_k_4700_);
            v_v_4701_ = lean_ctor_get(v_l_4694_, 2);
            lean_inc(v_v_4701_);
            v_l_4702_ = lean_ctor_get(v_l_4694_, 3);
            lean_inc(v_l_4702_);
            v_r_4703_ = lean_ctor_get(v_l_4694_, 4);
            lean_inc(v_r_4703_);
            lean_dec_ref_known(v_l_4694_, 5);
            v___x_4704_ = lean_apply_10(
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
            let mut v_size_4705_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4706_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4707_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4708_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4693_);
            v_size_4705_ = lean_ctor_get(v_x_4689_, 0);
            lean_inc(v_size_4705_);
            v_k_4706_ = lean_ctor_get(v_x_4689_, 1);
            lean_inc(v_k_4706_);
            v_v_4707_ = lean_ctor_get(v_x_4689_, 2);
            lean_inc(v_v_4707_);
            v_r_4708_ = lean_ctor_get(v_x_4689_, 4);
            lean_inc(v_r_4708_);
            lean_dec_ref_known(v_x_4689_, 5);
            v___x_4709_ = lean_apply_5(
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
        let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4693_);
        lean_dec(v_h__2_4692_);
        v___x_4710_ = lean_apply_1(v_h__1_4691_, v_x_4690_);
        return v___x_4710_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(
    mut v_x_4711_: *mut LeanObject,
    mut v_h__1_4712_: *mut LeanObject,
    mut v_h__2_4713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_l_4714_: *mut LeanObject = core::ptr::null_mut();
    v_l_4714_ = lean_ctor_get(v_x_4711_, 3);
    if lean_obj_tag(v_l_4714_) == 0 {
        let mut v_size_4715_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4716_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4717_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4718_: *mut LeanObject = core::ptr::null_mut();
        let mut v_size_4719_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4720_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4721_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4722_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_l_4714_);
        lean_dec(v_h__1_4712_);
        v_size_4715_ = lean_ctor_get(v_x_4711_, 0);
        lean_inc(v_size_4715_);
        v_k_4716_ = lean_ctor_get(v_x_4711_, 1);
        lean_inc(v_k_4716_);
        v_v_4717_ = lean_ctor_get(v_x_4711_, 2);
        lean_inc(v_v_4717_);
        v_r_4718_ = lean_ctor_get(v_x_4711_, 4);
        lean_inc(v_r_4718_);
        lean_dec(v_x_4711_);
        v_size_4719_ = lean_ctor_get(v_l_4714_, 0);
        lean_inc(v_size_4719_);
        v_k_4720_ = lean_ctor_get(v_l_4714_, 1);
        lean_inc(v_k_4720_);
        v_v_4721_ = lean_ctor_get(v_l_4714_, 2);
        lean_inc(v_v_4721_);
        v_l_4722_ = lean_ctor_get(v_l_4714_, 3);
        lean_inc(v_l_4722_);
        v_r_4723_ = lean_ctor_get(v_l_4714_, 4);
        lean_inc(v_r_4723_);
        lean_dec_ref_known(v_l_4714_, 5);
        v___x_4724_ = lean_apply_10(
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
            lean_box(0),
        );
        return v___x_4724_;
    } else {
        let mut v_size_4725_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4726_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4727_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4713_);
        v_size_4725_ = lean_ctor_get(v_x_4711_, 0);
        lean_inc(v_size_4725_);
        v_k_4726_ = lean_ctor_get(v_x_4711_, 1);
        lean_inc(v_k_4726_);
        v_v_4727_ = lean_ctor_get(v_x_4711_, 2);
        lean_inc(v_v_4727_);
        v_r_4728_ = lean_ctor_get(v_x_4711_, 4);
        lean_inc(v_r_4728_);
        lean_dec(v_x_4711_);
        v___x_4729_ = lean_apply_5(
            v_h__1_4712_,
            v_size_4725_,
            v_k_4726_,
            v_v_4727_,
            v_r_4728_,
            lean_box(0),
        );
        return v___x_4729_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(
    mut v_00_u03b1_4730_: *mut LeanObject,
    mut v_00_u03b2_4731_: *mut LeanObject,
    mut v_motive_4732_: *mut LeanObject,
    mut v_x_4733_: *mut LeanObject,
    mut v_x_4734_: *mut LeanObject,
    mut v_h__1_4735_: *mut LeanObject,
    mut v_h__2_4736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_l_4737_: *mut LeanObject = core::ptr::null_mut();
    v_l_4737_ = lean_ctor_get(v_x_4733_, 3);
    if lean_obj_tag(v_l_4737_) == 0 {
        let mut v_size_4738_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4739_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4740_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4741_: *mut LeanObject = core::ptr::null_mut();
        let mut v_size_4742_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4743_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4744_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4745_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_l_4737_);
        lean_dec(v_h__1_4735_);
        v_size_4738_ = lean_ctor_get(v_x_4733_, 0);
        lean_inc(v_size_4738_);
        v_k_4739_ = lean_ctor_get(v_x_4733_, 1);
        lean_inc(v_k_4739_);
        v_v_4740_ = lean_ctor_get(v_x_4733_, 2);
        lean_inc(v_v_4740_);
        v_r_4741_ = lean_ctor_get(v_x_4733_, 4);
        lean_inc(v_r_4741_);
        lean_dec(v_x_4733_);
        v_size_4742_ = lean_ctor_get(v_l_4737_, 0);
        lean_inc(v_size_4742_);
        v_k_4743_ = lean_ctor_get(v_l_4737_, 1);
        lean_inc(v_k_4743_);
        v_v_4744_ = lean_ctor_get(v_l_4737_, 2);
        lean_inc(v_v_4744_);
        v_l_4745_ = lean_ctor_get(v_l_4737_, 3);
        lean_inc(v_l_4745_);
        v_r_4746_ = lean_ctor_get(v_l_4737_, 4);
        lean_inc(v_r_4746_);
        lean_dec_ref_known(v_l_4737_, 5);
        v___x_4747_ = lean_apply_10(
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
            lean_box(0),
        );
        return v___x_4747_;
    } else {
        let mut v_size_4748_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4749_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4750_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4736_);
        v_size_4748_ = lean_ctor_get(v_x_4733_, 0);
        lean_inc(v_size_4748_);
        v_k_4749_ = lean_ctor_get(v_x_4733_, 1);
        lean_inc(v_k_4749_);
        v_v_4750_ = lean_ctor_get(v_x_4733_, 2);
        lean_inc(v_v_4750_);
        v_r_4751_ = lean_ctor_get(v_x_4733_, 4);
        lean_inc(v_r_4751_);
        lean_dec(v_x_4733_);
        v___x_4752_ = lean_apply_5(
            v_h__1_4735_,
            v_size_4748_,
            v_k_4749_,
            v_v_4750_,
            v_r_4751_,
            lean_box(0),
        );
        return v___x_4752_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(
    mut v_x_4753_: *mut LeanObject,
    mut v_h__1_4754_: *mut LeanObject,
    mut v_h__2_4755_: *mut LeanObject,
    mut v_h__3_4756_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4753_) == 0 {
        let mut v_r_4757_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4754_);
        v_r_4757_ = lean_ctor_get(v_x_4753_, 4);
        if lean_obj_tag(v_r_4757_) == 0 {
            let mut v_size_4758_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4759_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4760_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4761_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4762_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4763_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4764_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4765_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4766_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4757_);
            lean_dec(v_h__2_4755_);
            v_size_4758_ = lean_ctor_get(v_x_4753_, 0);
            lean_inc(v_size_4758_);
            v_k_4759_ = lean_ctor_get(v_x_4753_, 1);
            lean_inc(v_k_4759_);
            v_v_4760_ = lean_ctor_get(v_x_4753_, 2);
            lean_inc(v_v_4760_);
            v_l_4761_ = lean_ctor_get(v_x_4753_, 3);
            lean_inc(v_l_4761_);
            lean_dec_ref_known(v_x_4753_, 5);
            v_size_4762_ = lean_ctor_get(v_r_4757_, 0);
            lean_inc(v_size_4762_);
            v_k_4763_ = lean_ctor_get(v_r_4757_, 1);
            lean_inc(v_k_4763_);
            v_v_4764_ = lean_ctor_get(v_r_4757_, 2);
            lean_inc(v_v_4764_);
            v_l_4765_ = lean_ctor_get(v_r_4757_, 3);
            lean_inc(v_l_4765_);
            v_r_4766_ = lean_ctor_get(v_r_4757_, 4);
            lean_inc(v_r_4766_);
            lean_dec_ref_known(v_r_4757_, 5);
            v___x_4767_ = lean_apply_9(
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
            let mut v_size_4768_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4769_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4770_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4771_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4756_);
            v_size_4768_ = lean_ctor_get(v_x_4753_, 0);
            lean_inc(v_size_4768_);
            v_k_4769_ = lean_ctor_get(v_x_4753_, 1);
            lean_inc(v_k_4769_);
            v_v_4770_ = lean_ctor_get(v_x_4753_, 2);
            lean_inc(v_v_4770_);
            v_l_4771_ = lean_ctor_get(v_x_4753_, 3);
            lean_inc(v_l_4771_);
            lean_dec_ref_known(v_x_4753_, 5);
            v___x_4772_ = lean_apply_4(v_h__2_4755_, v_size_4768_, v_k_4769_, v_v_4770_, v_l_4771_);
            return v___x_4772_;
        }
    } else {
        let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4756_);
        lean_dec(v_h__2_4755_);
        v___x_4773_ = lean_box(0);
        v___x_4774_ = lean_apply_1(v_h__1_4754_, v___x_4773_);
        return v___x_4774_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(
    mut v_00_u03b1_4775_: *mut LeanObject,
    mut v_00_u03b2_4776_: *mut LeanObject,
    mut v_motive_4777_: *mut LeanObject,
    mut v_x_4778_: *mut LeanObject,
    mut v_h__1_4779_: *mut LeanObject,
    mut v_h__2_4780_: *mut LeanObject,
    mut v_h__3_4781_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4778_) == 0 {
        let mut v_r_4782_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4779_);
        v_r_4782_ = lean_ctor_get(v_x_4778_, 4);
        if lean_obj_tag(v_r_4782_) == 0 {
            let mut v_size_4783_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4784_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4785_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4786_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4787_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4788_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4789_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4790_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4791_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4782_);
            lean_dec(v_h__2_4780_);
            v_size_4783_ = lean_ctor_get(v_x_4778_, 0);
            lean_inc(v_size_4783_);
            v_k_4784_ = lean_ctor_get(v_x_4778_, 1);
            lean_inc(v_k_4784_);
            v_v_4785_ = lean_ctor_get(v_x_4778_, 2);
            lean_inc(v_v_4785_);
            v_l_4786_ = lean_ctor_get(v_x_4778_, 3);
            lean_inc(v_l_4786_);
            lean_dec_ref_known(v_x_4778_, 5);
            v_size_4787_ = lean_ctor_get(v_r_4782_, 0);
            lean_inc(v_size_4787_);
            v_k_4788_ = lean_ctor_get(v_r_4782_, 1);
            lean_inc(v_k_4788_);
            v_v_4789_ = lean_ctor_get(v_r_4782_, 2);
            lean_inc(v_v_4789_);
            v_l_4790_ = lean_ctor_get(v_r_4782_, 3);
            lean_inc(v_l_4790_);
            v_r_4791_ = lean_ctor_get(v_r_4782_, 4);
            lean_inc(v_r_4791_);
            lean_dec_ref_known(v_r_4782_, 5);
            v___x_4792_ = lean_apply_9(
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
            let mut v_size_4793_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4794_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4795_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4781_);
            v_size_4793_ = lean_ctor_get(v_x_4778_, 0);
            lean_inc(v_size_4793_);
            v_k_4794_ = lean_ctor_get(v_x_4778_, 1);
            lean_inc(v_k_4794_);
            v_v_4795_ = lean_ctor_get(v_x_4778_, 2);
            lean_inc(v_v_4795_);
            v_l_4796_ = lean_ctor_get(v_x_4778_, 3);
            lean_inc(v_l_4796_);
            lean_dec_ref_known(v_x_4778_, 5);
            v___x_4797_ = lean_apply_4(v_h__2_4780_, v_size_4793_, v_k_4794_, v_v_4795_, v_l_4796_);
            return v___x_4797_;
        }
    } else {
        let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4781_);
        lean_dec(v_h__2_4780_);
        v___x_4798_ = lean_box(0);
        v___x_4799_ = lean_apply_1(v_h__1_4779_, v___x_4798_);
        return v___x_4799_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(
    mut v_x_4800_: *mut LeanObject,
    mut v_x_4801_: *mut LeanObject,
    mut v_h__1_4802_: *mut LeanObject,
    mut v_h__2_4803_: *mut LeanObject,
    mut v_h__3_4804_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4800_) == 0 {
        let mut v_r_4805_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4802_);
        v_r_4805_ = lean_ctor_get(v_x_4800_, 4);
        if lean_obj_tag(v_r_4805_) == 0 {
            let mut v_size_4806_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4807_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4808_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4809_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4810_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4811_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4812_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4813_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4814_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4805_);
            lean_dec(v_h__2_4803_);
            v_size_4806_ = lean_ctor_get(v_x_4800_, 0);
            lean_inc(v_size_4806_);
            v_k_4807_ = lean_ctor_get(v_x_4800_, 1);
            lean_inc(v_k_4807_);
            v_v_4808_ = lean_ctor_get(v_x_4800_, 2);
            lean_inc(v_v_4808_);
            v_l_4809_ = lean_ctor_get(v_x_4800_, 3);
            lean_inc(v_l_4809_);
            lean_dec_ref_known(v_x_4800_, 5);
            v_size_4810_ = lean_ctor_get(v_r_4805_, 0);
            lean_inc(v_size_4810_);
            v_k_4811_ = lean_ctor_get(v_r_4805_, 1);
            lean_inc(v_k_4811_);
            v_v_4812_ = lean_ctor_get(v_r_4805_, 2);
            lean_inc(v_v_4812_);
            v_l_4813_ = lean_ctor_get(v_r_4805_, 3);
            lean_inc(v_l_4813_);
            v_r_4814_ = lean_ctor_get(v_r_4805_, 4);
            lean_inc(v_r_4814_);
            lean_dec_ref_known(v_r_4805_, 5);
            v___x_4815_ = lean_apply_10(
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
            let mut v_size_4816_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4817_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4818_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4819_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4804_);
            v_size_4816_ = lean_ctor_get(v_x_4800_, 0);
            lean_inc(v_size_4816_);
            v_k_4817_ = lean_ctor_get(v_x_4800_, 1);
            lean_inc(v_k_4817_);
            v_v_4818_ = lean_ctor_get(v_x_4800_, 2);
            lean_inc(v_v_4818_);
            v_l_4819_ = lean_ctor_get(v_x_4800_, 3);
            lean_inc(v_l_4819_);
            lean_dec_ref_known(v_x_4800_, 5);
            v___x_4820_ = lean_apply_5(
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
        let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4804_);
        lean_dec(v_h__2_4803_);
        v___x_4821_ = lean_apply_1(v_h__1_4802_, v_x_4801_);
        return v___x_4821_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(
    mut v_00_u03b1_4822_: *mut LeanObject,
    mut v_00_u03b2_4823_: *mut LeanObject,
    mut v_motive_4824_: *mut LeanObject,
    mut v_x_4825_: *mut LeanObject,
    mut v_x_4826_: *mut LeanObject,
    mut v_h__1_4827_: *mut LeanObject,
    mut v_h__2_4828_: *mut LeanObject,
    mut v_h__3_4829_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4825_) == 0 {
        let mut v_r_4830_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4827_);
        v_r_4830_ = lean_ctor_get(v_x_4825_, 4);
        if lean_obj_tag(v_r_4830_) == 0 {
            let mut v_size_4831_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4832_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4833_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4834_: *mut LeanObject = core::ptr::null_mut();
            let mut v_size_4835_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4836_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4837_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4838_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4839_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_r_4830_);
            lean_dec(v_h__2_4828_);
            v_size_4831_ = lean_ctor_get(v_x_4825_, 0);
            lean_inc(v_size_4831_);
            v_k_4832_ = lean_ctor_get(v_x_4825_, 1);
            lean_inc(v_k_4832_);
            v_v_4833_ = lean_ctor_get(v_x_4825_, 2);
            lean_inc(v_v_4833_);
            v_l_4834_ = lean_ctor_get(v_x_4825_, 3);
            lean_inc(v_l_4834_);
            lean_dec_ref_known(v_x_4825_, 5);
            v_size_4835_ = lean_ctor_get(v_r_4830_, 0);
            lean_inc(v_size_4835_);
            v_k_4836_ = lean_ctor_get(v_r_4830_, 1);
            lean_inc(v_k_4836_);
            v_v_4837_ = lean_ctor_get(v_r_4830_, 2);
            lean_inc(v_v_4837_);
            v_l_4838_ = lean_ctor_get(v_r_4830_, 3);
            lean_inc(v_l_4838_);
            v_r_4839_ = lean_ctor_get(v_r_4830_, 4);
            lean_inc(v_r_4839_);
            lean_dec_ref_known(v_r_4830_, 5);
            v___x_4840_ = lean_apply_10(
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
            let mut v_size_4841_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_4842_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4843_: *mut LeanObject = core::ptr::null_mut();
            let mut v_l_4844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_4829_);
            v_size_4841_ = lean_ctor_get(v_x_4825_, 0);
            lean_inc(v_size_4841_);
            v_k_4842_ = lean_ctor_get(v_x_4825_, 1);
            lean_inc(v_k_4842_);
            v_v_4843_ = lean_ctor_get(v_x_4825_, 2);
            lean_inc(v_v_4843_);
            v_l_4844_ = lean_ctor_get(v_x_4825_, 3);
            lean_inc(v_l_4844_);
            lean_dec_ref_known(v_x_4825_, 5);
            v___x_4845_ = lean_apply_5(
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
        let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_4829_);
        lean_dec(v_h__2_4828_);
        v___x_4846_ = lean_apply_1(v_h__1_4827_, v_x_4826_);
        return v___x_4846_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(
    mut v_x_4847_: *mut LeanObject,
    mut v_h__1_4848_: *mut LeanObject,
    mut v_h__2_4849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_4850_: *mut LeanObject = core::ptr::null_mut();
    v_r_4850_ = lean_ctor_get(v_x_4847_, 4);
    if lean_obj_tag(v_r_4850_) == 0 {
        let mut v_size_4851_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4852_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4853_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4854_: *mut LeanObject = core::ptr::null_mut();
        let mut v_size_4855_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4856_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4857_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4858_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_r_4850_);
        lean_dec(v_h__1_4848_);
        v_size_4851_ = lean_ctor_get(v_x_4847_, 0);
        lean_inc(v_size_4851_);
        v_k_4852_ = lean_ctor_get(v_x_4847_, 1);
        lean_inc(v_k_4852_);
        v_v_4853_ = lean_ctor_get(v_x_4847_, 2);
        lean_inc(v_v_4853_);
        v_l_4854_ = lean_ctor_get(v_x_4847_, 3);
        lean_inc(v_l_4854_);
        lean_dec(v_x_4847_);
        v_size_4855_ = lean_ctor_get(v_r_4850_, 0);
        lean_inc(v_size_4855_);
        v_k_4856_ = lean_ctor_get(v_r_4850_, 1);
        lean_inc(v_k_4856_);
        v_v_4857_ = lean_ctor_get(v_r_4850_, 2);
        lean_inc(v_v_4857_);
        v_l_4858_ = lean_ctor_get(v_r_4850_, 3);
        lean_inc(v_l_4858_);
        v_r_4859_ = lean_ctor_get(v_r_4850_, 4);
        lean_inc(v_r_4859_);
        lean_dec_ref_known(v_r_4850_, 5);
        v___x_4860_ = lean_apply_10(
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
            lean_box(0),
        );
        return v___x_4860_;
    } else {
        let mut v_size_4861_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4862_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4863_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4864_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4849_);
        v_size_4861_ = lean_ctor_get(v_x_4847_, 0);
        lean_inc(v_size_4861_);
        v_k_4862_ = lean_ctor_get(v_x_4847_, 1);
        lean_inc(v_k_4862_);
        v_v_4863_ = lean_ctor_get(v_x_4847_, 2);
        lean_inc(v_v_4863_);
        v_l_4864_ = lean_ctor_get(v_x_4847_, 3);
        lean_inc(v_l_4864_);
        lean_dec(v_x_4847_);
        v___x_4865_ = lean_apply_5(
            v_h__1_4848_,
            v_size_4861_,
            v_k_4862_,
            v_v_4863_,
            v_l_4864_,
            lean_box(0),
        );
        return v___x_4865_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(
    mut v_00_u03b1_4866_: *mut LeanObject,
    mut v_00_u03b2_4867_: *mut LeanObject,
    mut v_motive_4868_: *mut LeanObject,
    mut v_x_4869_: *mut LeanObject,
    mut v_x_4870_: *mut LeanObject,
    mut v_h__1_4871_: *mut LeanObject,
    mut v_h__2_4872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_4873_: *mut LeanObject = core::ptr::null_mut();
    v_r_4873_ = lean_ctor_get(v_x_4869_, 4);
    if lean_obj_tag(v_r_4873_) == 0 {
        let mut v_size_4874_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4875_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4876_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4877_: *mut LeanObject = core::ptr::null_mut();
        let mut v_size_4878_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4879_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4880_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4881_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_r_4873_);
        lean_dec(v_h__1_4871_);
        v_size_4874_ = lean_ctor_get(v_x_4869_, 0);
        lean_inc(v_size_4874_);
        v_k_4875_ = lean_ctor_get(v_x_4869_, 1);
        lean_inc(v_k_4875_);
        v_v_4876_ = lean_ctor_get(v_x_4869_, 2);
        lean_inc(v_v_4876_);
        v_l_4877_ = lean_ctor_get(v_x_4869_, 3);
        lean_inc(v_l_4877_);
        lean_dec(v_x_4869_);
        v_size_4878_ = lean_ctor_get(v_r_4873_, 0);
        lean_inc(v_size_4878_);
        v_k_4879_ = lean_ctor_get(v_r_4873_, 1);
        lean_inc(v_k_4879_);
        v_v_4880_ = lean_ctor_get(v_r_4873_, 2);
        lean_inc(v_v_4880_);
        v_l_4881_ = lean_ctor_get(v_r_4873_, 3);
        lean_inc(v_l_4881_);
        v_r_4882_ = lean_ctor_get(v_r_4873_, 4);
        lean_inc(v_r_4882_);
        lean_dec_ref_known(v_r_4873_, 5);
        v___x_4883_ = lean_apply_10(
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
            lean_box(0),
        );
        return v___x_4883_;
    } else {
        let mut v_size_4884_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4885_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4886_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4872_);
        v_size_4884_ = lean_ctor_get(v_x_4869_, 0);
        lean_inc(v_size_4884_);
        v_k_4885_ = lean_ctor_get(v_x_4869_, 1);
        lean_inc(v_k_4885_);
        v_v_4886_ = lean_ctor_get(v_x_4869_, 2);
        lean_inc(v_v_4886_);
        v_l_4887_ = lean_ctor_get(v_x_4869_, 3);
        lean_inc(v_l_4887_);
        lean_dec(v_x_4869_);
        v___x_4888_ = lean_apply_5(
            v_h__1_4871_,
            v_size_4884_,
            v_k_4885_,
            v_v_4886_,
            v_l_4887_,
            lean_box(0),
        );
        return v___x_4888_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___redArg(
    mut v_l_4889_: *mut LeanObject,
    mut v_h__1_4890_: *mut LeanObject,
    mut v_h__2_4891_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_4889_) == 0 {
        let mut v_size_4892_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4893_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4894_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4895_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4890_);
        v_size_4892_ = lean_ctor_get(v_l_4889_, 0);
        lean_inc(v_size_4892_);
        v_k_4893_ = lean_ctor_get(v_l_4889_, 1);
        lean_inc(v_k_4893_);
        v_v_4894_ = lean_ctor_get(v_l_4889_, 2);
        lean_inc(v_v_4894_);
        v_l_4895_ = lean_ctor_get(v_l_4889_, 3);
        lean_inc(v_l_4895_);
        v_r_4896_ = lean_ctor_get(v_l_4889_, 4);
        lean_inc(v_r_4896_);
        lean_dec_ref_known(v_l_4889_, 5);
        v___x_4897_ = lean_apply_7(
            v_h__2_4891_,
            v_size_4892_,
            v_k_4893_,
            v_v_4894_,
            v_l_4895_,
            v_r_4896_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_4897_;
    } else {
        let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4891_);
        v___x_4898_ = lean_apply_2(v_h__1_4890_, lean_box(0), lean_box(0));
        return v___x_4898_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(
    mut v_00_u03b1_4899_: *mut LeanObject,
    mut v_00_u03b2_4900_: *mut LeanObject,
    mut v_r_4901_: *mut LeanObject,
    mut v_motive_4902_: *mut LeanObject,
    mut v_l_4903_: *mut LeanObject,
    mut v_hl_4904_: *mut LeanObject,
    mut v_hlr_4905_: *mut LeanObject,
    mut v_h__1_4906_: *mut LeanObject,
    mut v_h__2_4907_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_4903_) == 0 {
        let mut v_size_4908_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4909_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4910_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4911_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4906_);
        v_size_4908_ = lean_ctor_get(v_l_4903_, 0);
        lean_inc(v_size_4908_);
        v_k_4909_ = lean_ctor_get(v_l_4903_, 1);
        lean_inc(v_k_4909_);
        v_v_4910_ = lean_ctor_get(v_l_4903_, 2);
        lean_inc(v_v_4910_);
        v_l_4911_ = lean_ctor_get(v_l_4903_, 3);
        lean_inc(v_l_4911_);
        v_r_4912_ = lean_ctor_get(v_l_4903_, 4);
        lean_inc(v_r_4912_);
        lean_dec_ref_known(v_l_4903_, 5);
        v___x_4913_ = lean_apply_7(
            v_h__2_4907_,
            v_size_4908_,
            v_k_4909_,
            v_v_4910_,
            v_l_4911_,
            v_r_4912_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_4913_;
    } else {
        let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4907_);
        v___x_4914_ = lean_apply_2(v_h__1_4906_, lean_box(0), lean_box(0));
        return v___x_4914_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter___boxed(
    mut v_00_u03b1_4915_: *mut LeanObject,
    mut v_00_u03b2_4916_: *mut LeanObject,
    mut v_r_4917_: *mut LeanObject,
    mut v_motive_4918_: *mut LeanObject,
    mut v_l_4919_: *mut LeanObject,
    mut v_hl_4920_: *mut LeanObject,
    mut v_hlr_4921_: *mut LeanObject,
    mut v_h__1_4922_: *mut LeanObject,
    mut v_h__2_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4924_: *mut LeanObject = core::ptr::null_mut();
    v_res_4924_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__3_splitter(v_00_u03b1_4915_, v_00_u03b2_4916_, v_r_4917_, v_motive_4918_, v_l_4919_, v_hl_4920_, v_hlr_4921_, v_h__1_4922_, v_h__2_4923_);
    lean_dec(v_r_4917_);
    return v_res_4924_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___redArg(
    mut v_x_4925_: *mut LeanObject,
    mut v_h__1_4926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    v_k_4927_ = lean_ctor_get(v_x_4925_, 0);
    lean_inc(v_k_4927_);
    v_v_4928_ = lean_ctor_get(v_x_4925_, 1);
    lean_inc(v_v_4928_);
    v_tree_4929_ = lean_ctor_get(v_x_4925_, 2);
    lean_inc(v_tree_4929_);
    lean_dec_ref(v_x_4925_);
    v___x_4930_ = lean_apply_5(
        v_h__1_4926_,
        v_k_4927_,
        v_v_4928_,
        v_tree_4929_,
        lean_box(0),
        lean_box(0),
    );
    return v___x_4930_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(
    mut v_00_u03b1_4931_: *mut LeanObject,
    mut v_00_u03b2_4932_: *mut LeanObject,
    mut v_l_x27_4933_: *mut LeanObject,
    mut v_r_x27_4934_: *mut LeanObject,
    mut v_motive_4935_: *mut LeanObject,
    mut v_x_4936_: *mut LeanObject,
    mut v_h__1_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    v_k_4938_ = lean_ctor_get(v_x_4936_, 0);
    lean_inc(v_k_4938_);
    v_v_4939_ = lean_ctor_get(v_x_4936_, 1);
    lean_inc(v_v_4939_);
    v_tree_4940_ = lean_ctor_get(v_x_4936_, 2);
    lean_inc(v_tree_4940_);
    lean_dec_ref(v_x_4936_);
    v___x_4941_ = lean_apply_5(
        v_h__1_4937_,
        v_k_4938_,
        v_v_4939_,
        v_tree_4940_,
        lean_box(0),
        lean_box(0),
    );
    return v___x_4941_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter___boxed(
    mut v_00_u03b1_4942_: *mut LeanObject,
    mut v_00_u03b2_4943_: *mut LeanObject,
    mut v_l_x27_4944_: *mut LeanObject,
    mut v_r_x27_4945_: *mut LeanObject,
    mut v_motive_4946_: *mut LeanObject,
    mut v_x_4947_: *mut LeanObject,
    mut v_h__1_4948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4949_: *mut LeanObject = core::ptr::null_mut();
    v_res_4949_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_match__1_splitter(v_00_u03b1_4942_, v_00_u03b2_4943_, v_l_x27_4944_, v_r_x27_4945_, v_motive_4946_, v_x_4947_, v_h__1_4948_);
    lean_dec(v_r_x27_4945_);
    lean_dec(v_l_x27_4944_);
    return v_res_4949_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter___redArg(
    mut v_l_4950_: *mut LeanObject,
    mut v_h__1_4951_: *mut LeanObject,
    mut v_h__2_4952_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_4950_) == 0 {
        let mut v_size_4953_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4954_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4955_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4956_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4951_);
        v_size_4953_ = lean_ctor_get(v_l_4950_, 0);
        lean_inc(v_size_4953_);
        v_k_4954_ = lean_ctor_get(v_l_4950_, 1);
        lean_inc(v_k_4954_);
        v_v_4955_ = lean_ctor_get(v_l_4950_, 2);
        lean_inc(v_v_4955_);
        v_l_4956_ = lean_ctor_get(v_l_4950_, 3);
        lean_inc(v_l_4956_);
        v_r_4957_ = lean_ctor_get(v_l_4950_, 4);
        lean_inc(v_r_4957_);
        lean_dec_ref_known(v_l_4950_, 5);
        v___x_4958_ = lean_apply_5(
            v_h__2_4952_,
            v_size_4953_,
            v_k_4954_,
            v_v_4955_,
            v_l_4956_,
            v_r_4957_,
        );
        return v___x_4958_;
    } else {
        let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4952_);
        v___x_4959_ = lean_box(0);
        v___x_4960_ = lean_apply_1(v_h__1_4951_, v___x_4959_);
        return v___x_4960_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_minView_x21_match__1_splitter(
    mut v_00_u03b1_4961_: *mut LeanObject,
    mut v_00_u03b2_4962_: *mut LeanObject,
    mut v_motive_4963_: *mut LeanObject,
    mut v_l_4964_: *mut LeanObject,
    mut v_h__1_4965_: *mut LeanObject,
    mut v_h__2_4966_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_4964_) == 0 {
        let mut v_size_4967_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4968_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4969_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4970_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4965_);
        v_size_4967_ = lean_ctor_get(v_l_4964_, 0);
        lean_inc(v_size_4967_);
        v_k_4968_ = lean_ctor_get(v_l_4964_, 1);
        lean_inc(v_k_4968_);
        v_v_4969_ = lean_ctor_get(v_l_4964_, 2);
        lean_inc(v_v_4969_);
        v_l_4970_ = lean_ctor_get(v_l_4964_, 3);
        lean_inc(v_l_4970_);
        v_r_4971_ = lean_ctor_get(v_l_4964_, 4);
        lean_inc(v_r_4971_);
        lean_dec_ref_known(v_l_4964_, 5);
        v___x_4972_ = lean_apply_5(
            v_h__2_4966_,
            v_size_4967_,
            v_k_4968_,
            v_v_4969_,
            v_l_4970_,
            v_r_4971_,
        );
        return v___x_4972_;
    } else {
        let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4966_);
        v___x_4973_ = lean_box(0);
        v___x_4974_ = lean_apply_1(v_h__1_4965_, v___x_4973_);
        return v___x_4974_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___redArg(
    mut v_r_4975_: *mut LeanObject,
    mut v_h__1_4976_: *mut LeanObject,
    mut v_h__2_4977_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_4975_) == 0 {
        let mut v_size_4978_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4979_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4980_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4981_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4976_);
        v_size_4978_ = lean_ctor_get(v_r_4975_, 0);
        lean_inc(v_size_4978_);
        v_k_4979_ = lean_ctor_get(v_r_4975_, 1);
        lean_inc(v_k_4979_);
        v_v_4980_ = lean_ctor_get(v_r_4975_, 2);
        lean_inc(v_v_4980_);
        v_l_4981_ = lean_ctor_get(v_r_4975_, 3);
        lean_inc(v_l_4981_);
        v_r_4982_ = lean_ctor_get(v_r_4975_, 4);
        lean_inc(v_r_4982_);
        lean_dec_ref_known(v_r_4975_, 5);
        v___x_4983_ = lean_apply_7(
            v_h__2_4977_,
            v_size_4978_,
            v_k_4979_,
            v_v_4980_,
            v_l_4981_,
            v_r_4982_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_4983_;
    } else {
        let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4977_);
        v___x_4984_ = lean_apply_2(v_h__1_4976_, lean_box(0), lean_box(0));
        return v___x_4984_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(
    mut v_00_u03b1_4985_: *mut LeanObject,
    mut v_00_u03b2_4986_: *mut LeanObject,
    mut v_l_4987_: *mut LeanObject,
    mut v_motive_4988_: *mut LeanObject,
    mut v_r_4989_: *mut LeanObject,
    mut v_hr_4990_: *mut LeanObject,
    mut v_hlr_4991_: *mut LeanObject,
    mut v_h__1_4992_: *mut LeanObject,
    mut v_h__2_4993_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_4989_) == 0 {
        let mut v_size_4994_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_4995_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_4996_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_4997_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_4998_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_4992_);
        v_size_4994_ = lean_ctor_get(v_r_4989_, 0);
        lean_inc(v_size_4994_);
        v_k_4995_ = lean_ctor_get(v_r_4989_, 1);
        lean_inc(v_k_4995_);
        v_v_4996_ = lean_ctor_get(v_r_4989_, 2);
        lean_inc(v_v_4996_);
        v_l_4997_ = lean_ctor_get(v_r_4989_, 3);
        lean_inc(v_l_4997_);
        v_r_4998_ = lean_ctor_get(v_r_4989_, 4);
        lean_inc(v_r_4998_);
        lean_dec_ref_known(v_r_4989_, 5);
        v___x_4999_ = lean_apply_7(
            v_h__2_4993_,
            v_size_4994_,
            v_k_4995_,
            v_v_4996_,
            v_l_4997_,
            v_r_4998_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_4999_;
    } else {
        let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_4993_);
        v___x_5000_ = lean_apply_2(v_h__1_4992_, lean_box(0), lean_box(0));
        return v___x_5000_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter___boxed(
    mut v_00_u03b1_5001_: *mut LeanObject,
    mut v_00_u03b2_5002_: *mut LeanObject,
    mut v_l_5003_: *mut LeanObject,
    mut v_motive_5004_: *mut LeanObject,
    mut v_r_5005_: *mut LeanObject,
    mut v_hr_5006_: *mut LeanObject,
    mut v_hlr_5007_: *mut LeanObject,
    mut v_h__1_5008_: *mut LeanObject,
    mut v_h__2_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5010_: *mut LeanObject = core::ptr::null_mut();
    v_res_5010_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_maxView_match__1_splitter(v_00_u03b1_5001_, v_00_u03b2_5002_, v_l_5003_, v_motive_5004_, v_r_5005_, v_hr_5006_, v_hlr_5007_, v_h__1_5008_, v_h__2_5009_);
    lean_dec(v_l_5003_);
    return v_res_5010_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___redArg(
    mut v_r_5011_: *mut LeanObject,
    mut v_h__1_5012_: *mut LeanObject,
    mut v_h__2_5013_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_5011_) == 0 {
        let mut v_size_5014_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5015_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5016_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5017_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5012_);
        v_size_5014_ = lean_ctor_get(v_r_5011_, 0);
        lean_inc(v_size_5014_);
        v_k_5015_ = lean_ctor_get(v_r_5011_, 1);
        lean_inc(v_k_5015_);
        v_v_5016_ = lean_ctor_get(v_r_5011_, 2);
        lean_inc(v_v_5016_);
        v_l_5017_ = lean_ctor_get(v_r_5011_, 3);
        lean_inc(v_l_5017_);
        v_r_5018_ = lean_ctor_get(v_r_5011_, 4);
        lean_inc(v_r_5018_);
        lean_dec_ref_known(v_r_5011_, 5);
        v___x_5019_ = lean_apply_7(
            v_h__2_5013_,
            v_size_5014_,
            v_k_5015_,
            v_v_5016_,
            v_l_5017_,
            v_r_5018_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5019_;
    } else {
        let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5013_);
        v___x_5020_ = lean_apply_2(v_h__1_5012_, lean_box(0), lean_box(0));
        return v___x_5020_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(
    mut v_00_u03b1_5021_: *mut LeanObject,
    mut v_00_u03b2_5022_: *mut LeanObject,
    mut v_sz_5023_: *mut LeanObject,
    mut v_k_5024_: *mut LeanObject,
    mut v_v_5025_: *mut LeanObject,
    mut v_l_x27_5026_: *mut LeanObject,
    mut v_r_x27_5027_: *mut LeanObject,
    mut v_motive_5028_: *mut LeanObject,
    mut v_r_5029_: *mut LeanObject,
    mut v_hr_5030_: *mut LeanObject,
    mut v_hlr_5031_: *mut LeanObject,
    mut v_h__1_5032_: *mut LeanObject,
    mut v_h__2_5033_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_5029_) == 0 {
        let mut v_size_5034_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5035_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5036_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5037_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5032_);
        v_size_5034_ = lean_ctor_get(v_r_5029_, 0);
        lean_inc(v_size_5034_);
        v_k_5035_ = lean_ctor_get(v_r_5029_, 1);
        lean_inc(v_k_5035_);
        v_v_5036_ = lean_ctor_get(v_r_5029_, 2);
        lean_inc(v_v_5036_);
        v_l_5037_ = lean_ctor_get(v_r_5029_, 3);
        lean_inc(v_l_5037_);
        v_r_5038_ = lean_ctor_get(v_r_5029_, 4);
        lean_inc(v_r_5038_);
        lean_dec_ref_known(v_r_5029_, 5);
        v___x_5039_ = lean_apply_7(
            v_h__2_5033_,
            v_size_5034_,
            v_k_5035_,
            v_v_5036_,
            v_l_5037_,
            v_r_5038_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5039_;
    } else {
        let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5033_);
        v___x_5040_ = lean_apply_2(v_h__1_5032_, lean_box(0), lean_box(0));
        return v___x_5040_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter___boxed(
    mut v_00_u03b1_5041_: *mut LeanObject,
    mut v_00_u03b2_5042_: *mut LeanObject,
    mut v_sz_5043_: *mut LeanObject,
    mut v_k_5044_: *mut LeanObject,
    mut v_v_5045_: *mut LeanObject,
    mut v_l_x27_5046_: *mut LeanObject,
    mut v_r_x27_5047_: *mut LeanObject,
    mut v_motive_5048_: *mut LeanObject,
    mut v_r_5049_: *mut LeanObject,
    mut v_hr_5050_: *mut LeanObject,
    mut v_hlr_5051_: *mut LeanObject,
    mut v_h__1_5052_: *mut LeanObject,
    mut v_h__2_5053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5054_: *mut LeanObject = core::ptr::null_mut();
    v_res_5054_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_match__1_splitter(v_00_u03b1_5041_, v_00_u03b2_5042_, v_sz_5043_, v_k_5044_, v_v_5045_, v_l_x27_5046_, v_r_x27_5047_, v_motive_5048_, v_r_5049_, v_hr_5050_, v_hlr_5051_, v_h__1_5052_, v_h__2_5053_);
    lean_dec(v_r_x27_5047_);
    lean_dec(v_l_x27_5046_);
    lean_dec(v_v_5045_);
    lean_dec(v_k_5044_);
    lean_dec(v_sz_5043_);
    return v_res_5054_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter___redArg(
    mut v_t_5055_: *mut LeanObject,
    mut v_h__1_5056_: *mut LeanObject,
    mut v_h__2_5057_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_5055_) == 0 {
        let mut v_size_5058_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5059_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5060_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5061_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5056_);
        v_size_5058_ = lean_ctor_get(v_t_5055_, 0);
        lean_inc(v_size_5058_);
        v_k_5059_ = lean_ctor_get(v_t_5055_, 1);
        lean_inc(v_k_5059_);
        v_v_5060_ = lean_ctor_get(v_t_5055_, 2);
        lean_inc(v_v_5060_);
        v_l_5061_ = lean_ctor_get(v_t_5055_, 3);
        lean_inc(v_l_5061_);
        v_r_5062_ = lean_ctor_get(v_t_5055_, 4);
        lean_inc(v_r_5062_);
        lean_dec_ref_known(v_t_5055_, 5);
        v___x_5063_ = lean_apply_6(
            v_h__2_5057_,
            v_size_5058_,
            v_k_5059_,
            v_v_5060_,
            v_l_5061_,
            v_r_5062_,
            lean_box(0),
        );
        return v___x_5063_;
    } else {
        let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5057_);
        v___x_5064_ = lean_apply_1(v_h__1_5056_, lean_box(0));
        return v___x_5064_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__3_splitter(
    mut v_00_u03b1_5065_: *mut LeanObject,
    mut v_00_u03b2_5066_: *mut LeanObject,
    mut v_motive_5067_: *mut LeanObject,
    mut v_t_5068_: *mut LeanObject,
    mut v_hr_5069_: *mut LeanObject,
    mut v_h__1_5070_: *mut LeanObject,
    mut v_h__2_5071_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_5068_) == 0 {
        let mut v_size_5072_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5073_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5074_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5075_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5070_);
        v_size_5072_ = lean_ctor_get(v_t_5068_, 0);
        lean_inc(v_size_5072_);
        v_k_5073_ = lean_ctor_get(v_t_5068_, 1);
        lean_inc(v_k_5073_);
        v_v_5074_ = lean_ctor_get(v_t_5068_, 2);
        lean_inc(v_v_5074_);
        v_l_5075_ = lean_ctor_get(v_t_5068_, 3);
        lean_inc(v_l_5075_);
        v_r_5076_ = lean_ctor_get(v_t_5068_, 4);
        lean_inc(v_r_5076_);
        lean_dec_ref_known(v_t_5068_, 5);
        v___x_5077_ = lean_apply_6(
            v_h__2_5071_,
            v_size_5072_,
            v_k_5073_,
            v_v_5074_,
            v_l_5075_,
            v_r_5076_,
            lean_box(0),
        );
        return v___x_5077_;
    } else {
        let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5071_);
        v___x_5078_ = lean_apply_1(v_h__1_5070_, lean_box(0));
        return v___x_5078_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(
    mut v_x_5079_: u8,
    mut v_h__1_5080_: *mut LeanObject,
    mut v_h__2_5081_: *mut LeanObject,
    mut v_h__3_5082_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5079_ {
        0 => {
            let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5082_);
            lean_dec(v_h__2_5081_);
            v___x_5083_ = lean_box(0);
            v___x_5084_ = lean_apply_1(v_h__1_5080_, v___x_5083_);
            return v___x_5084_;
        }
        1 => {
            let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5081_);
            lean_dec(v_h__1_5080_);
            v___x_5085_ = lean_box(0);
            v___x_5086_ = lean_apply_1(v_h__3_5082_, v___x_5085_);
            return v___x_5086_;
        }
        _ => {
            let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5082_);
            lean_dec(v_h__1_5080_);
            v___x_5087_ = lean_box(0);
            v___x_5088_ = lean_apply_1(v_h__2_5081_, v___x_5087_);
            return v___x_5088_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg___boxed(
    mut v_x_5089_: *mut LeanObject,
    mut v_h__1_5090_: *mut LeanObject,
    mut v_h__2_5091_: *mut LeanObject,
    mut v_h__3_5092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_5093_: u8 = 0;
    let mut v_res_5094_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_5093_ = (lean_unbox(v_x_5089_) as u8);
    v_res_5094_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___redArg(v_x_36__boxed_5093_, v_h__1_5090_, v_h__2_5091_, v_h__3_5092_);
    return v_res_5094_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(
    mut v_motive_5095_: *mut LeanObject,
    mut v_x_5096_: u8,
    mut v_h__1_5097_: *mut LeanObject,
    mut v_h__2_5098_: *mut LeanObject,
    mut v_h__3_5099_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5096_ {
        0 => {
            let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5099_);
            lean_dec(v_h__2_5098_);
            v___x_5100_ = lean_box(0);
            v___x_5101_ = lean_apply_1(v_h__1_5097_, v___x_5100_);
            return v___x_5101_;
        }
        1 => {
            let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5098_);
            lean_dec(v_h__1_5097_);
            v___x_5102_ = lean_box(0);
            v___x_5103_ = lean_apply_1(v_h__3_5099_, v___x_5102_);
            return v___x_5103_;
        }
        _ => {
            let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5099_);
            lean_dec(v_h__1_5097_);
            v___x_5104_ = lean_box(0);
            v___x_5105_ = lean_apply_1(v_h__2_5098_, v___x_5104_);
            return v___x_5105_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter___boxed(
    mut v_motive_5106_: *mut LeanObject,
    mut v_x_5107_: *mut LeanObject,
    mut v_h__1_5108_: *mut LeanObject,
    mut v_h__2_5109_: *mut LeanObject,
    mut v_h__3_5110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_5111_: u8 = 0;
    let mut v_res_5112_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_5111_ = (lean_unbox(v_x_5107_) as u8);
    v_res_5112_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__3_splitter(v_motive_5106_, v_x_51__boxed_5111_, v_h__1_5108_, v_h__2_5109_, v_h__3_5110_);
    return v_res_5112_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___redArg(
    mut v_x_5113_: *mut LeanObject,
    mut v_h__1_5114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    v___x_5115_ = lean_apply_4(
        v_h__1_5114_,
        v_x_5113_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_5115_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(
    mut v_00_u03b1_5116_: *mut LeanObject,
    mut v_00_u03b2_5117_: *mut LeanObject,
    mut v_l_x27_5118_: *mut LeanObject,
    mut v_motive_5119_: *mut LeanObject,
    mut v_x_5120_: *mut LeanObject,
    mut v_h__1_5121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    v___x_5122_ = lean_apply_4(
        v_h__1_5121_,
        v_x_5120_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_5122_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter___boxed(
    mut v_00_u03b1_5123_: *mut LeanObject,
    mut v_00_u03b2_5124_: *mut LeanObject,
    mut v_l_x27_5125_: *mut LeanObject,
    mut v_motive_5126_: *mut LeanObject,
    mut v_x_5127_: *mut LeanObject,
    mut v_h__1_5128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5129_: *mut LeanObject = core::ptr::null_mut();
    v_res_5129_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insert_match__1_splitter(v_00_u03b1_5123_, v_00_u03b2_5124_, v_l_x27_5125_, v_motive_5126_, v_x_5127_, v_h__1_5128_);
    lean_dec(v_l_x27_5125_);
    return v_res_5129_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter___redArg(
    mut v_l_5130_: *mut LeanObject,
    mut v_h__1_5131_: *mut LeanObject,
    mut v_h__2_5132_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_5130_) == 0 {
        let mut v_size_5133_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5134_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5135_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5136_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5131_);
        v_size_5133_ = lean_ctor_get(v_l_5130_, 0);
        lean_inc(v_size_5133_);
        v_k_5134_ = lean_ctor_get(v_l_5130_, 1);
        lean_inc(v_k_5134_);
        v_v_5135_ = lean_ctor_get(v_l_5130_, 2);
        lean_inc(v_v_5135_);
        v_l_5136_ = lean_ctor_get(v_l_5130_, 3);
        lean_inc(v_l_5136_);
        v_r_5137_ = lean_ctor_get(v_l_5130_, 4);
        lean_inc(v_r_5137_);
        lean_dec_ref_known(v_l_5130_, 5);
        v___x_5138_ = lean_apply_6(
            v_h__2_5132_,
            v_size_5133_,
            v_k_5134_,
            v_v_5135_,
            v_l_5136_,
            v_r_5137_,
            lean_box(0),
        );
        return v___x_5138_;
    } else {
        let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5132_);
        v___x_5139_ = lean_apply_1(v_h__1_5131_, lean_box(0));
        return v___x_5139_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__5_splitter(
    mut v_00_u03b1_5140_: *mut LeanObject,
    mut v_00_u03b2_5141_: *mut LeanObject,
    mut v_motive_5142_: *mut LeanObject,
    mut v_l_5143_: *mut LeanObject,
    mut v_hl_5144_: *mut LeanObject,
    mut v_h__1_5145_: *mut LeanObject,
    mut v_h__2_5146_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_5143_) == 0 {
        let mut v_size_5147_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5148_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5149_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5150_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5145_);
        v_size_5147_ = lean_ctor_get(v_l_5143_, 0);
        lean_inc(v_size_5147_);
        v_k_5148_ = lean_ctor_get(v_l_5143_, 1);
        lean_inc(v_k_5148_);
        v_v_5149_ = lean_ctor_get(v_l_5143_, 2);
        lean_inc(v_v_5149_);
        v_l_5150_ = lean_ctor_get(v_l_5143_, 3);
        lean_inc(v_l_5150_);
        v_r_5151_ = lean_ctor_get(v_l_5143_, 4);
        lean_inc(v_r_5151_);
        lean_dec_ref_known(v_l_5143_, 5);
        v___x_5152_ = lean_apply_6(
            v_h__2_5146_,
            v_size_5147_,
            v_k_5148_,
            v_v_5149_,
            v_l_5150_,
            v_r_5151_,
            lean_box(0),
        );
        return v___x_5152_;
    } else {
        let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5146_);
        v___x_5153_ = lean_apply_1(v_h__1_5145_, lean_box(0));
        return v___x_5153_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter___redArg(
    mut v_x_5154_: *mut LeanObject,
    mut v_h__1_5155_: *mut LeanObject,
    mut v_h__2_5156_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5154_) == 0 {
        let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5156_);
        v___x_5157_ = lean_box(0);
        v___x_5158_ = lean_apply_1(v_h__1_5155_, v___x_5157_);
        return v___x_5158_;
    } else {
        let mut v_val_5159_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_5160_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_5161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5155_);
        v_val_5159_ = lean_ctor_get(v_x_5154_, 0);
        lean_inc(v_val_5159_);
        lean_dec_ref_known(v_x_5154_, 1);
        v_fst_5160_ = lean_ctor_get(v_val_5159_, 0);
        lean_inc(v_fst_5160_);
        v_snd_5161_ = lean_ctor_get(v_val_5159_, 1);
        lean_inc(v_snd_5161_);
        lean_dec(v_val_5159_);
        v___x_5162_ = lean_apply_2(v_h__2_5156_, v_fst_5160_, v_snd_5161_);
        return v___x_5162_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__1_splitter(
    mut v_00_u03b1_5163_: *mut LeanObject,
    mut v_00_u03b2_5164_: *mut LeanObject,
    mut v_motive_5165_: *mut LeanObject,
    mut v_x_5166_: *mut LeanObject,
    mut v_h__1_5167_: *mut LeanObject,
    mut v_h__2_5168_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5166_) == 0 {
        let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5168_);
        v___x_5169_ = lean_box(0);
        v___x_5170_ = lean_apply_1(v_h__1_5167_, v___x_5169_);
        return v___x_5170_;
    } else {
        let mut v_val_5171_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_5172_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_5173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5167_);
        v_val_5171_ = lean_ctor_get(v_x_5166_, 0);
        lean_inc(v_val_5171_);
        lean_dec_ref_known(v_x_5166_, 1);
        v_fst_5172_ = lean_ctor_get(v_val_5171_, 0);
        lean_inc(v_fst_5172_);
        v_snd_5173_ = lean_ctor_get(v_val_5171_, 1);
        lean_inc(v_snd_5173_);
        lean_dec(v_val_5171_);
        v___x_5174_ = lean_apply_2(v_h__2_5168_, v_fst_5172_, v_snd_5173_);
        return v___x_5174_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___redArg(
    mut v_x_5175_: *mut LeanObject,
    mut v_h__1_5176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    v___x_5177_ = lean_apply_4(
        v_h__1_5176_,
        v_x_5175_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_5177_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(
    mut v_00_u03b1_5178_: *mut LeanObject,
    mut v_00_u03b2_5179_: *mut LeanObject,
    mut v_l_5180_: *mut LeanObject,
    mut v_motive_5181_: *mut LeanObject,
    mut v_x_5182_: *mut LeanObject,
    mut v_h__1_5183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    v___x_5184_ = lean_apply_4(
        v_h__1_5183_,
        v_x_5182_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_5184_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter___boxed(
    mut v_00_u03b1_5185_: *mut LeanObject,
    mut v_00_u03b2_5186_: *mut LeanObject,
    mut v_l_5187_: *mut LeanObject,
    mut v_motive_5188_: *mut LeanObject,
    mut v_x_5189_: *mut LeanObject,
    mut v_h__1_5190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5191_: *mut LeanObject = core::ptr::null_mut();
    v_res_5191_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_updateCell_match__3_splitter(v_00_u03b1_5185_, v_00_u03b2_5186_, v_l_5187_, v_motive_5188_, v_x_5189_, v_h__1_5190_);
    lean_dec(v_l_5187_);
    return v_res_5191_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___redArg(
    mut v_x_5192_: *mut LeanObject,
    mut v_h__1_5193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    v___x_5194_ = lean_apply_4(
        v_h__1_5193_,
        v_x_5192_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_5194_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(
    mut v_00_u03b1_5195_: *mut LeanObject,
    mut v_00_u03b2_5196_: *mut LeanObject,
    mut v_l_5197_: *mut LeanObject,
    mut v_motive_5198_: *mut LeanObject,
    mut v_x_5199_: *mut LeanObject,
    mut v_h__1_5200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    v___x_5201_ = lean_apply_4(
        v_h__1_5200_,
        v_x_5199_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_5201_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter___boxed(
    mut v_00_u03b1_5202_: *mut LeanObject,
    mut v_00_u03b2_5203_: *mut LeanObject,
    mut v_l_5204_: *mut LeanObject,
    mut v_motive_5205_: *mut LeanObject,
    mut v_x_5206_: *mut LeanObject,
    mut v_h__1_5207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5208_: *mut LeanObject = core::ptr::null_mut();
    v_res_5208_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_erase_match__1_splitter(v_00_u03b1_5202_, v_00_u03b2_5203_, v_l_5204_, v_motive_5205_, v_x_5206_, v_h__1_5207_);
    lean_dec(v_l_5204_);
    return v_res_5208_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___redArg(
    mut v_x_5209_: *mut LeanObject,
    mut v_h__1_5210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    v___x_5211_ = lean_apply_3(v_h__1_5210_, v_x_5209_, lean_box(0), lean_box(0));
    return v___x_5211_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(
    mut v_00_u03b1_5212_: *mut LeanObject,
    mut v_00_u03b2_5213_: *mut LeanObject,
    mut v_l_x27_5214_: *mut LeanObject,
    mut v_motive_5215_: *mut LeanObject,
    mut v_x_5216_: *mut LeanObject,
    mut v_h__1_5217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    v___x_5218_ = lean_apply_3(v_h__1_5217_, v_x_5216_, lean_box(0), lean_box(0));
    return v___x_5218_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter___boxed(
    mut v_00_u03b1_5219_: *mut LeanObject,
    mut v_00_u03b2_5220_: *mut LeanObject,
    mut v_l_x27_5221_: *mut LeanObject,
    mut v_motive_5222_: *mut LeanObject,
    mut v_x_5223_: *mut LeanObject,
    mut v_h__1_5224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5225_: *mut LeanObject = core::ptr::null_mut();
    v_res_5225_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMin_match__1_splitter(v_00_u03b1_5219_, v_00_u03b2_5220_, v_l_x27_5221_, v_motive_5222_, v_x_5223_, v_h__1_5224_);
    lean_dec(v_l_x27_5221_);
    return v_res_5225_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___redArg(
    mut v_x_5226_: *mut LeanObject,
    mut v_h__1_5227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    v___x_5228_ = lean_apply_3(v_h__1_5227_, v_x_5226_, lean_box(0), lean_box(0));
    return v___x_5228_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(
    mut v_00_u03b1_5229_: *mut LeanObject,
    mut v_00_u03b2_5230_: *mut LeanObject,
    mut v_r_x27_5231_: *mut LeanObject,
    mut v_motive_5232_: *mut LeanObject,
    mut v_x_5233_: *mut LeanObject,
    mut v_h__1_5234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    v___x_5235_ = lean_apply_3(v_h__1_5234_, v_x_5233_, lean_box(0), lean_box(0));
    return v___x_5235_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter___boxed(
    mut v_00_u03b1_5236_: *mut LeanObject,
    mut v_00_u03b2_5237_: *mut LeanObject,
    mut v_r_x27_5238_: *mut LeanObject,
    mut v_motive_5239_: *mut LeanObject,
    mut v_x_5240_: *mut LeanObject,
    mut v_h__1_5241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5242_: *mut LeanObject = core::ptr::null_mut();
    v_res_5242_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_insertMax_match__1_splitter(v_00_u03b1_5236_, v_00_u03b2_5237_, v_r_x27_5238_, v_motive_5239_, v_x_5240_, v_h__1_5241_);
    lean_dec(v_r_x27_5238_);
    return v_res_5242_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter___redArg(
    mut v_r_5243_: *mut LeanObject,
    mut v_h__1_5244_: *mut LeanObject,
    mut v_h__2_5245_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_5243_) == 0 {
        let mut v_size_5246_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5247_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5248_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5249_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5244_);
        v_size_5246_ = lean_ctor_get(v_r_5243_, 0);
        lean_inc(v_size_5246_);
        v_k_5247_ = lean_ctor_get(v_r_5243_, 1);
        lean_inc(v_k_5247_);
        v_v_5248_ = lean_ctor_get(v_r_5243_, 2);
        lean_inc(v_v_5248_);
        v_l_5249_ = lean_ctor_get(v_r_5243_, 3);
        lean_inc(v_l_5249_);
        v_r_5250_ = lean_ctor_get(v_r_5243_, 4);
        lean_inc(v_r_5250_);
        lean_dec_ref_known(v_r_5243_, 5);
        v___x_5251_ = lean_apply_5(
            v_h__2_5245_,
            v_size_5246_,
            v_k_5247_,
            v_v_5248_,
            v_l_5249_,
            v_r_5250_,
        );
        return v___x_5251_;
    } else {
        let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5245_);
        v___x_5252_ = lean_box(0);
        v___x_5253_ = lean_apply_1(v_h__1_5244_, v___x_5252_);
        return v___x_5253_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_glue_x21_match__1_splitter(
    mut v_00_u03b1_5254_: *mut LeanObject,
    mut v_00_u03b2_5255_: *mut LeanObject,
    mut v_motive_5256_: *mut LeanObject,
    mut v_r_5257_: *mut LeanObject,
    mut v_h__1_5258_: *mut LeanObject,
    mut v_h__2_5259_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_5257_) == 0 {
        let mut v_size_5260_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5261_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5262_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5263_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5258_);
        v_size_5260_ = lean_ctor_get(v_r_5257_, 0);
        lean_inc(v_size_5260_);
        v_k_5261_ = lean_ctor_get(v_r_5257_, 1);
        lean_inc(v_k_5261_);
        v_v_5262_ = lean_ctor_get(v_r_5257_, 2);
        lean_inc(v_v_5262_);
        v_l_5263_ = lean_ctor_get(v_r_5257_, 3);
        lean_inc(v_l_5263_);
        v_r_5264_ = lean_ctor_get(v_r_5257_, 4);
        lean_inc(v_r_5264_);
        lean_dec_ref_known(v_r_5257_, 5);
        v___x_5265_ = lean_apply_5(
            v_h__2_5259_,
            v_size_5260_,
            v_k_5261_,
            v_v_5262_,
            v_l_5263_,
            v_r_5264_,
        );
        return v___x_5265_;
    } else {
        let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5259_);
        v___x_5266_ = lean_box(0);
        v___x_5267_ = lean_apply_1(v_h__1_5258_, v___x_5266_);
        return v___x_5267_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter___redArg(
    mut v_x_5268_: *mut LeanObject,
    mut v_h__1_5269_: *mut LeanObject,
    mut v_h__2_5270_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5268_) == 0 {
        let mut v_size_5271_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5272_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5273_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5274_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5270_);
        v_size_5271_ = lean_ctor_get(v_x_5268_, 0);
        lean_inc(v_size_5271_);
        v_k_5272_ = lean_ctor_get(v_x_5268_, 1);
        lean_inc(v_k_5272_);
        v_v_5273_ = lean_ctor_get(v_x_5268_, 2);
        lean_inc(v_v_5273_);
        v_l_5274_ = lean_ctor_get(v_x_5268_, 3);
        lean_inc(v_l_5274_);
        v_r_5275_ = lean_ctor_get(v_x_5268_, 4);
        lean_inc(v_r_5275_);
        lean_dec_ref_known(v_x_5268_, 5);
        v___x_5276_ = lean_apply_5(
            v_h__1_5269_,
            v_size_5271_,
            v_k_5272_,
            v_v_5273_,
            v_l_5274_,
            v_r_5275_,
        );
        return v___x_5276_;
    } else {
        let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5269_);
        v___x_5277_ = lean_box(0);
        v___x_5278_ = lean_apply_1(v_h__2_5270_, v___x_5277_);
        return v___x_5278_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_size_match__1_splitter(
    mut v_00_u03b1_5279_: *mut LeanObject,
    mut v_00_u03b2_5280_: *mut LeanObject,
    mut v_motive_5281_: *mut LeanObject,
    mut v_x_5282_: *mut LeanObject,
    mut v_h__1_5283_: *mut LeanObject,
    mut v_h__2_5284_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5282_) == 0 {
        let mut v_size_5285_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5286_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5287_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5288_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5284_);
        v_size_5285_ = lean_ctor_get(v_x_5282_, 0);
        lean_inc(v_size_5285_);
        v_k_5286_ = lean_ctor_get(v_x_5282_, 1);
        lean_inc(v_k_5286_);
        v_v_5287_ = lean_ctor_get(v_x_5282_, 2);
        lean_inc(v_v_5287_);
        v_l_5288_ = lean_ctor_get(v_x_5282_, 3);
        lean_inc(v_l_5288_);
        v_r_5289_ = lean_ctor_get(v_x_5282_, 4);
        lean_inc(v_r_5289_);
        lean_dec_ref_known(v_x_5282_, 5);
        v___x_5290_ = lean_apply_5(
            v_h__1_5283_,
            v_size_5285_,
            v_k_5286_,
            v_v_5287_,
            v_l_5288_,
            v_r_5289_,
        );
        return v___x_5290_;
    } else {
        let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5283_);
        v___x_5291_ = lean_box(0);
        v___x_5292_ = lean_apply_1(v_h__2_5284_, v___x_5291_);
        return v___x_5292_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter___redArg(
    mut v_r_5293_: *mut LeanObject,
    mut v_h__1_5294_: *mut LeanObject,
    mut v_h__2_5295_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_5293_) == 0 {
        let mut v_size_5296_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5297_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5298_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5299_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5294_);
        v_size_5296_ = lean_ctor_get(v_r_5293_, 0);
        lean_inc(v_size_5296_);
        v_k_5297_ = lean_ctor_get(v_r_5293_, 1);
        lean_inc(v_k_5297_);
        v_v_5298_ = lean_ctor_get(v_r_5293_, 2);
        lean_inc(v_v_5298_);
        v_l_5299_ = lean_ctor_get(v_r_5293_, 3);
        lean_inc(v_l_5299_);
        v_r_5300_ = lean_ctor_get(v_r_5293_, 4);
        lean_inc(v_r_5300_);
        lean_dec_ref_known(v_r_5293_, 5);
        v___x_5301_ = lean_apply_7(
            v_h__2_5295_,
            v_size_5296_,
            v_k_5297_,
            v_v_5298_,
            v_l_5299_,
            v_r_5300_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5301_;
    } else {
        let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5295_);
        v___x_5302_ = lean_apply_2(v_h__1_5294_, lean_box(0), lean_box(0));
        return v___x_5302_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_link2_match__5_splitter(
    mut v_00_u03b1_5303_: *mut LeanObject,
    mut v_00_u03b2_5304_: *mut LeanObject,
    mut v_motive_5305_: *mut LeanObject,
    mut v_r_5306_: *mut LeanObject,
    mut v_hr_5307_: *mut LeanObject,
    mut v_h__1_5308_: *mut LeanObject,
    mut v_h__2_5309_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_5306_) == 0 {
        let mut v_size_5310_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5311_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5312_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5313_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5308_);
        v_size_5310_ = lean_ctor_get(v_r_5306_, 0);
        lean_inc(v_size_5310_);
        v_k_5311_ = lean_ctor_get(v_r_5306_, 1);
        lean_inc(v_k_5311_);
        v_v_5312_ = lean_ctor_get(v_r_5306_, 2);
        lean_inc(v_v_5312_);
        v_l_5313_ = lean_ctor_get(v_r_5306_, 3);
        lean_inc(v_l_5313_);
        v_r_5314_ = lean_ctor_get(v_r_5306_, 4);
        lean_inc(v_r_5314_);
        lean_dec_ref_known(v_r_5306_, 5);
        v___x_5315_ = lean_apply_7(
            v_h__2_5309_,
            v_size_5310_,
            v_k_5311_,
            v_v_5312_,
            v_l_5313_,
            v_r_5314_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5315_;
    } else {
        let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5309_);
        v___x_5316_ = lean_apply_2(v_h__1_5308_, lean_box(0), lean_box(0));
        return v___x_5316_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter___redArg(
    mut v_t_5317_: *mut LeanObject,
    mut v_h__1_5318_: *mut LeanObject,
    mut v_h__2_5319_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_5317_) == 0 {
        let mut v_size_5320_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5321_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5322_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5323_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5318_);
        v_size_5320_ = lean_ctor_get(v_t_5317_, 0);
        lean_inc(v_size_5320_);
        v_k_5321_ = lean_ctor_get(v_t_5317_, 1);
        lean_inc(v_k_5321_);
        v_v_5322_ = lean_ctor_get(v_t_5317_, 2);
        lean_inc(v_v_5322_);
        v_l_5323_ = lean_ctor_get(v_t_5317_, 3);
        lean_inc(v_l_5323_);
        v_r_5324_ = lean_ctor_get(v_t_5317_, 4);
        lean_inc(v_r_5324_);
        lean_dec_ref_known(v_t_5317_, 5);
        v___x_5325_ = lean_apply_5(
            v_h__2_5319_,
            v_size_5320_,
            v_k_5321_,
            v_v_5322_,
            v_l_5323_,
            v_r_5324_,
        );
        return v___x_5325_;
    } else {
        let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5319_);
        v___x_5326_ = lean_box(0);
        v___x_5327_ = lean_apply_1(v_h__1_5318_, v___x_5326_);
        return v___x_5327_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_x3f_match__1_splitter(
    mut v_00_u03b1_5328_: *mut LeanObject,
    mut v_00_u03b4_5329_: *mut LeanObject,
    mut v_motive_5330_: *mut LeanObject,
    mut v_t_5331_: *mut LeanObject,
    mut v_h__1_5332_: *mut LeanObject,
    mut v_h__2_5333_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_5331_) == 0 {
        let mut v_size_5334_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5335_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5336_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5337_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5332_);
        v_size_5334_ = lean_ctor_get(v_t_5331_, 0);
        lean_inc(v_size_5334_);
        v_k_5335_ = lean_ctor_get(v_t_5331_, 1);
        lean_inc(v_k_5335_);
        v_v_5336_ = lean_ctor_get(v_t_5331_, 2);
        lean_inc(v_v_5336_);
        v_l_5337_ = lean_ctor_get(v_t_5331_, 3);
        lean_inc(v_l_5337_);
        v_r_5338_ = lean_ctor_get(v_t_5331_, 4);
        lean_inc(v_r_5338_);
        lean_dec_ref_known(v_t_5331_, 5);
        v___x_5339_ = lean_apply_5(
            v_h__2_5333_,
            v_size_5334_,
            v_k_5335_,
            v_v_5336_,
            v_l_5337_,
            v_r_5338_,
        );
        return v___x_5339_;
    } else {
        let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5333_);
        v___x_5340_ = lean_box(0);
        v___x_5341_ = lean_apply_1(v_h__1_5332_, v___x_5340_);
        return v___x_5341_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter___redArg(
    mut v_x_5342_: *mut LeanObject,
    mut v_h__1_5343_: *mut LeanObject,
    mut v_h__2_5344_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5342_) == 0 {
        let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5344_);
        v___x_5345_ = lean_box(0);
        v___x_5346_ = lean_apply_1(v_h__1_5343_, v___x_5345_);
        return v___x_5346_;
    } else {
        let mut v_val_5347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5343_);
        v_val_5347_ = lean_ctor_get(v_x_5342_, 0);
        lean_inc(v_val_5347_);
        lean_dec_ref_known(v_x_5342_, 1);
        v___x_5348_ = lean_apply_1(v_h__2_5344_, v_val_5347_);
        return v___x_5348_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Cell_Const_get_x3f_match__1_splitter(
    mut v_00_u03b1_5349_: *mut LeanObject,
    mut v_00_u03b2_5350_: *mut LeanObject,
    mut v_motive_5351_: *mut LeanObject,
    mut v_x_5352_: *mut LeanObject,
    mut v_h__1_5353_: *mut LeanObject,
    mut v_h__2_5354_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5352_) == 0 {
        let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5354_);
        v___x_5355_ = lean_box(0);
        v___x_5356_ = lean_apply_1(v_h__1_5353_, v___x_5355_);
        return v___x_5356_;
    } else {
        let mut v_val_5357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5353_);
        v_val_5357_ = lean_ctor_get(v_x_5352_, 0);
        lean_inc(v_val_5357_);
        lean_dec_ref_known(v_x_5352_, 1);
        v___x_5358_ = lean_apply_1(v_h__2_5354_, v_val_5357_);
        return v___x_5358_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___redArg(
    mut v_t_5359_: *mut LeanObject,
    mut v_h__1_5360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    v_size_5361_ = lean_ctor_get(v_t_5359_, 0);
    lean_inc(v_size_5361_);
    v_k_5362_ = lean_ctor_get(v_t_5359_, 1);
    lean_inc(v_k_5362_);
    v_v_5363_ = lean_ctor_get(v_t_5359_, 2);
    lean_inc(v_v_5363_);
    v_l_5364_ = lean_ctor_get(v_t_5359_, 3);
    lean_inc(v_l_5364_);
    v_r_5365_ = lean_ctor_get(v_t_5359_, 4);
    lean_inc(v_r_5365_);
    lean_dec(v_t_5359_);
    v___x_5366_ = lean_apply_6(
        v_h__1_5360_,
        v_size_5361_,
        v_k_5362_,
        v_v_5363_,
        v_l_5364_,
        v_r_5365_,
        lean_box(0),
    );
    return v___x_5366_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(
    mut v_00_u03b1_5367_: *mut LeanObject,
    mut v_00_u03b4_5368_: *mut LeanObject,
    mut v_inst_5369_: *mut LeanObject,
    mut v_k_5370_: *mut LeanObject,
    mut v_motive_5371_: *mut LeanObject,
    mut v_t_5372_: *mut LeanObject,
    mut v_hlk_5373_: *mut LeanObject,
    mut v_h__1_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    v_size_5375_ = lean_ctor_get(v_t_5372_, 0);
    lean_inc(v_size_5375_);
    v_k_5376_ = lean_ctor_get(v_t_5372_, 1);
    lean_inc(v_k_5376_);
    v_v_5377_ = lean_ctor_get(v_t_5372_, 2);
    lean_inc(v_v_5377_);
    v_l_5378_ = lean_ctor_get(v_t_5372_, 3);
    lean_inc(v_l_5378_);
    v_r_5379_ = lean_ctor_get(v_t_5372_, 4);
    lean_inc(v_r_5379_);
    lean_dec(v_t_5372_);
    v___x_5380_ = lean_apply_6(
        v_h__1_5374_,
        v_size_5375_,
        v_k_5376_,
        v_v_5377_,
        v_l_5378_,
        v_r_5379_,
        lean_box(0),
    );
    return v___x_5380_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter___boxed(
    mut v_00_u03b1_5381_: *mut LeanObject,
    mut v_00_u03b4_5382_: *mut LeanObject,
    mut v_inst_5383_: *mut LeanObject,
    mut v_k_5384_: *mut LeanObject,
    mut v_motive_5385_: *mut LeanObject,
    mut v_t_5386_: *mut LeanObject,
    mut v_hlk_5387_: *mut LeanObject,
    mut v_h__1_5388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5389_: *mut LeanObject = core::ptr::null_mut();
    v_res_5389_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_get_match__1_splitter(v_00_u03b1_5381_, v_00_u03b4_5382_, v_inst_5383_, v_k_5384_, v_motive_5385_, v_t_5386_, v_hlk_5387_, v_h__1_5388_);
    lean_dec(v_k_5384_);
    lean_dec_ref(v_inst_5383_);
    return v_res_5389_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter___redArg(
    mut v_x_5390_: *mut LeanObject,
    mut v_x_5391_: *mut LeanObject,
    mut v_h__1_5392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    v_size_5393_ = lean_ctor_get(v_x_5390_, 0);
    lean_inc(v_size_5393_);
    v_k_5394_ = lean_ctor_get(v_x_5390_, 1);
    lean_inc(v_k_5394_);
    v_v_5395_ = lean_ctor_get(v_x_5390_, 2);
    lean_inc(v_v_5395_);
    v_l_5396_ = lean_ctor_get(v_x_5390_, 3);
    lean_inc(v_l_5396_);
    v_r_5397_ = lean_ctor_get(v_x_5390_, 4);
    lean_inc(v_r_5397_);
    lean_dec(v_x_5390_);
    v___x_5398_ = lean_apply_8(
        v_h__1_5392_,
        v_size_5393_,
        v_k_5394_,
        v_v_5395_,
        v_l_5396_,
        v_r_5397_,
        lean_box(0),
        v_x_5391_,
        lean_box(0),
    );
    return v___x_5398_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__3_splitter(
    mut v_00_u03b1_5399_: *mut LeanObject,
    mut v_00_u03b2_5400_: *mut LeanObject,
    mut v_motive_5401_: *mut LeanObject,
    mut v_x_5402_: *mut LeanObject,
    mut v_x_5403_: *mut LeanObject,
    mut v_x_5404_: *mut LeanObject,
    mut v_x_5405_: *mut LeanObject,
    mut v_h__1_5406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    v_size_5407_ = lean_ctor_get(v_x_5402_, 0);
    lean_inc(v_size_5407_);
    v_k_5408_ = lean_ctor_get(v_x_5402_, 1);
    lean_inc(v_k_5408_);
    v_v_5409_ = lean_ctor_get(v_x_5402_, 2);
    lean_inc(v_v_5409_);
    v_l_5410_ = lean_ctor_get(v_x_5402_, 3);
    lean_inc(v_l_5410_);
    v_r_5411_ = lean_ctor_get(v_x_5402_, 4);
    lean_inc(v_r_5411_);
    lean_dec(v_x_5402_);
    v___x_5412_ = lean_apply_8(
        v_h__1_5406_,
        v_size_5407_,
        v_k_5408_,
        v_v_5409_,
        v_l_5410_,
        v_r_5411_,
        lean_box(0),
        v_x_5404_,
        lean_box(0),
    );
    return v___x_5412_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(
    mut v_x_5413_: u8,
    mut v_h__1_5414_: *mut LeanObject,
    mut v_h__2_5415_: *mut LeanObject,
    mut v_h__3_5416_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5413_ {
        0 => {
            let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5416_);
            lean_dec(v_h__2_5415_);
            v___x_5417_ = lean_apply_1(v_h__1_5414_, lean_box(0));
            return v___x_5417_;
        }
        1 => {
            let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5416_);
            lean_dec(v_h__1_5414_);
            v___x_5418_ = lean_apply_1(v_h__2_5415_, lean_box(0));
            return v___x_5418_;
        }
        _ => {
            let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5415_);
            lean_dec(v_h__1_5414_);
            v___x_5419_ = lean_apply_1(v_h__3_5416_, lean_box(0));
            return v___x_5419_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg___boxed(
    mut v_x_5420_: *mut LeanObject,
    mut v_h__1_5421_: *mut LeanObject,
    mut v_h__2_5422_: *mut LeanObject,
    mut v_h__3_5423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_5424_: u8 = 0;
    let mut v_res_5425_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_5424_ = (lean_unbox(v_x_5420_) as u8);
    v_res_5425_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___redArg(v_x_33__boxed_5424_, v_h__1_5421_, v_h__2_5422_, v_h__3_5423_);
    return v_res_5425_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(
    mut v_motive_5426_: *mut LeanObject,
    mut v_x_5427_: u8,
    mut v_h__1_5428_: *mut LeanObject,
    mut v_h__2_5429_: *mut LeanObject,
    mut v_h__3_5430_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5427_ {
        0 => {
            let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5430_);
            lean_dec(v_h__2_5429_);
            v___x_5431_ = lean_apply_1(v_h__1_5428_, lean_box(0));
            return v___x_5431_;
        }
        1 => {
            let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5430_);
            lean_dec(v_h__1_5428_);
            v___x_5432_ = lean_apply_1(v_h__2_5429_, lean_box(0));
            return v___x_5432_;
        }
        _ => {
            let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5429_);
            lean_dec(v_h__1_5428_);
            v___x_5433_ = lean_apply_1(v_h__3_5430_, lean_box(0));
            return v___x_5433_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter___boxed(
    mut v_motive_5434_: *mut LeanObject,
    mut v_x_5435_: *mut LeanObject,
    mut v_h__1_5436_: *mut LeanObject,
    mut v_h__2_5437_: *mut LeanObject,
    mut v_h__3_5438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_42__boxed_5439_: u8 = 0;
    let mut v_res_5440_: *mut LeanObject = core::ptr::null_mut();
    v_x_42__boxed_5439_ = (lean_unbox(v_x_5435_) as u8);
    v_res_5440_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_match__1_splitter(v_motive_5434_, v_x_42__boxed_5439_, v_h__1_5436_, v_h__2_5437_, v_h__3_5438_);
    return v_res_5440_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter___redArg(
    mut v_x_5441_: *mut LeanObject,
    mut v_x_5442_: *mut LeanObject,
    mut v_h__1_5443_: *mut LeanObject,
    mut v_h__2_5444_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5441_) == 0 {
        let mut v_size_5445_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5446_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5447_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5448_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5443_);
        v_size_5445_ = lean_ctor_get(v_x_5441_, 0);
        lean_inc(v_size_5445_);
        v_k_5446_ = lean_ctor_get(v_x_5441_, 1);
        lean_inc(v_k_5446_);
        v_v_5447_ = lean_ctor_get(v_x_5441_, 2);
        lean_inc(v_v_5447_);
        v_l_5448_ = lean_ctor_get(v_x_5441_, 3);
        lean_inc(v_l_5448_);
        v_r_5449_ = lean_ctor_get(v_x_5441_, 4);
        lean_inc(v_r_5449_);
        lean_dec_ref_known(v_x_5441_, 5);
        v___x_5450_ = lean_apply_6(
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
        let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5444_);
        v___x_5451_ = lean_apply_1(v_h__1_5443_, v_x_5442_);
        return v___x_5451_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__3_splitter(
    mut v_00_u03b1_5452_: *mut LeanObject,
    mut v_00_u03b2_5453_: *mut LeanObject,
    mut v_motive_5454_: *mut LeanObject,
    mut v_x_5455_: *mut LeanObject,
    mut v_x_5456_: *mut LeanObject,
    mut v_h__1_5457_: *mut LeanObject,
    mut v_h__2_5458_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5455_) == 0 {
        let mut v_size_5459_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5460_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5461_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5462_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5463_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5457_);
        v_size_5459_ = lean_ctor_get(v_x_5455_, 0);
        lean_inc(v_size_5459_);
        v_k_5460_ = lean_ctor_get(v_x_5455_, 1);
        lean_inc(v_k_5460_);
        v_v_5461_ = lean_ctor_get(v_x_5455_, 2);
        lean_inc(v_v_5461_);
        v_l_5462_ = lean_ctor_get(v_x_5455_, 3);
        lean_inc(v_l_5462_);
        v_r_5463_ = lean_ctor_get(v_x_5455_, 4);
        lean_inc(v_r_5463_);
        lean_dec_ref_known(v_x_5455_, 5);
        v___x_5464_ = lean_apply_6(
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
        let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5458_);
        v___x_5465_ = lean_apply_1(v_h__1_5457_, v_x_5456_);
        return v___x_5465_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(
    mut v_x_5466_: u8,
    mut v_h__1_5467_: *mut LeanObject,
    mut v_h__2_5468_: *mut LeanObject,
    mut v_h__3_5469_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5466_ {
        0 => {
            let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5469_);
            lean_dec(v_h__2_5468_);
            v___x_5470_ = lean_box(0);
            v___x_5471_ = lean_apply_1(v_h__1_5467_, v___x_5470_);
            return v___x_5471_;
        }
        1 => {
            let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5469_);
            lean_dec(v_h__1_5467_);
            v___x_5472_ = lean_box(0);
            v___x_5473_ = lean_apply_1(v_h__2_5468_, v___x_5472_);
            return v___x_5473_;
        }
        _ => {
            let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5468_);
            lean_dec(v_h__1_5467_);
            v___x_5474_ = lean_box(0);
            v___x_5475_ = lean_apply_1(v_h__3_5469_, v___x_5474_);
            return v___x_5475_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg___boxed(
    mut v_x_5476_: *mut LeanObject,
    mut v_h__1_5477_: *mut LeanObject,
    mut v_h__2_5478_: *mut LeanObject,
    mut v_h__3_5479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_5480_: u8 = 0;
    let mut v_res_5481_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_5480_ = (lean_unbox(v_x_5476_) as u8);
    v_res_5481_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___redArg(v_x_36__boxed_5480_, v_h__1_5477_, v_h__2_5478_, v_h__3_5479_);
    return v_res_5481_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(
    mut v_motive_5482_: *mut LeanObject,
    mut v_x_5483_: u8,
    mut v_h__1_5484_: *mut LeanObject,
    mut v_h__2_5485_: *mut LeanObject,
    mut v_h__3_5486_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5483_ {
        0 => {
            let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5486_);
            lean_dec(v_h__2_5485_);
            v___x_5487_ = lean_box(0);
            v___x_5488_ = lean_apply_1(v_h__1_5484_, v___x_5487_);
            return v___x_5488_;
        }
        1 => {
            let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5486_);
            lean_dec(v_h__1_5484_);
            v___x_5489_ = lean_box(0);
            v___x_5490_ = lean_apply_1(v_h__2_5485_, v___x_5489_);
            return v___x_5490_;
        }
        _ => {
            let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5485_);
            lean_dec(v_h__1_5484_);
            v___x_5491_ = lean_box(0);
            v___x_5492_ = lean_apply_1(v_h__3_5486_, v___x_5491_);
            return v___x_5492_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter___boxed(
    mut v_motive_5493_: *mut LeanObject,
    mut v_x_5494_: *mut LeanObject,
    mut v_h__1_5495_: *mut LeanObject,
    mut v_h__2_5496_: *mut LeanObject,
    mut v_h__3_5497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_5498_: u8 = 0;
    let mut v_res_5499_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_5498_ = (lean_unbox(v_x_5494_) as u8);
    v_res_5499_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdx_x3f_match__1_splitter(v_motive_5493_, v_x_51__boxed_5498_, v_h__1_5495_, v_h__2_5496_, v_h__3_5497_);
    return v_res_5499_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter___redArg(
    mut v_x_5500_: *mut LeanObject,
    mut v_x_5501_: *mut LeanObject,
    mut v_x_5502_: *mut LeanObject,
    mut v_h__1_5503_: *mut LeanObject,
    mut v_h__2_5504_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5500_) == 0 {
        let mut v_size_5505_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5506_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5507_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5508_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5503_);
        v_size_5505_ = lean_ctor_get(v_x_5500_, 0);
        lean_inc(v_size_5505_);
        v_k_5506_ = lean_ctor_get(v_x_5500_, 1);
        lean_inc(v_k_5506_);
        v_v_5507_ = lean_ctor_get(v_x_5500_, 2);
        lean_inc(v_v_5507_);
        v_l_5508_ = lean_ctor_get(v_x_5500_, 3);
        lean_inc(v_l_5508_);
        v_r_5509_ = lean_ctor_get(v_x_5500_, 4);
        lean_inc(v_r_5509_);
        lean_dec_ref_known(v_x_5500_, 5);
        v___x_5510_ = lean_apply_7(
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
        let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5504_);
        v___x_5511_ = lean_apply_2(v_h__1_5503_, v_x_5501_, v_x_5502_);
        return v___x_5511_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_entryAtIdxD_match__1_splitter(
    mut v_00_u03b1_5512_: *mut LeanObject,
    mut v_00_u03b2_5513_: *mut LeanObject,
    mut v_motive_5514_: *mut LeanObject,
    mut v_x_5515_: *mut LeanObject,
    mut v_x_5516_: *mut LeanObject,
    mut v_x_5517_: *mut LeanObject,
    mut v_h__1_5518_: *mut LeanObject,
    mut v_h__2_5519_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5515_) == 0 {
        let mut v_size_5520_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5521_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5522_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5523_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5518_);
        v_size_5520_ = lean_ctor_get(v_x_5515_, 0);
        lean_inc(v_size_5520_);
        v_k_5521_ = lean_ctor_get(v_x_5515_, 1);
        lean_inc(v_k_5521_);
        v_v_5522_ = lean_ctor_get(v_x_5515_, 2);
        lean_inc(v_v_5522_);
        v_l_5523_ = lean_ctor_get(v_x_5515_, 3);
        lean_inc(v_l_5523_);
        v_r_5524_ = lean_ctor_get(v_x_5515_, 4);
        lean_inc(v_r_5524_);
        lean_dec_ref_known(v_x_5515_, 5);
        v___x_5525_ = lean_apply_7(
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
        let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5519_);
        v___x_5526_ = lean_apply_2(v_h__1_5518_, v_x_5516_, v_x_5517_);
        return v___x_5526_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter___redArg(
    mut v_x_5527_: *mut LeanObject,
    mut v_x_5528_: *mut LeanObject,
    mut v_x_5529_: *mut LeanObject,
    mut v_h__1_5530_: *mut LeanObject,
    mut v_h__2_5531_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5527_) == 0 {
        let mut v_size_5532_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5533_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5534_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5535_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5530_);
        v_size_5532_ = lean_ctor_get(v_x_5527_, 0);
        lean_inc(v_size_5532_);
        v_k_5533_ = lean_ctor_get(v_x_5527_, 1);
        lean_inc(v_k_5533_);
        v_v_5534_ = lean_ctor_get(v_x_5527_, 2);
        lean_inc(v_v_5534_);
        v_l_5535_ = lean_ctor_get(v_x_5527_, 3);
        lean_inc(v_l_5535_);
        v_r_5536_ = lean_ctor_get(v_x_5527_, 4);
        lean_inc(v_r_5536_);
        lean_dec_ref_known(v_x_5527_, 5);
        v___x_5537_ = lean_apply_7(
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
        let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5531_);
        v___x_5538_ = lean_apply_2(v_h__1_5530_, v_x_5528_, v_x_5529_);
        return v___x_5538_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_keyAtIdxD_match__1_splitter(
    mut v_00_u03b1_5539_: *mut LeanObject,
    mut v_00_u03b2_5540_: *mut LeanObject,
    mut v_motive_5541_: *mut LeanObject,
    mut v_x_5542_: *mut LeanObject,
    mut v_x_5543_: *mut LeanObject,
    mut v_x_5544_: *mut LeanObject,
    mut v_h__1_5545_: *mut LeanObject,
    mut v_h__2_5546_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5542_) == 0 {
        let mut v_size_5547_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5548_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5549_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5550_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5545_);
        v_size_5547_ = lean_ctor_get(v_x_5542_, 0);
        lean_inc(v_size_5547_);
        v_k_5548_ = lean_ctor_get(v_x_5542_, 1);
        lean_inc(v_k_5548_);
        v_v_5549_ = lean_ctor_get(v_x_5542_, 2);
        lean_inc(v_v_5549_);
        v_l_5550_ = lean_ctor_get(v_x_5542_, 3);
        lean_inc(v_l_5550_);
        v_r_5551_ = lean_ctor_get(v_x_5542_, 4);
        lean_inc(v_r_5551_);
        lean_dec_ref_known(v_x_5542_, 5);
        v___x_5552_ = lean_apply_7(
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
        let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5546_);
        v___x_5553_ = lean_apply_2(v_h__1_5545_, v_x_5543_, v_x_5544_);
        return v___x_5553_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(
    mut v_x_5554_: *mut LeanObject,
    mut v_c_5555_: *mut LeanObject,
    mut v_x_5556_: *mut LeanObject,
    mut v_r_5557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5562_: u8 = 0;
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_c_5555_) == 0 {
                    v___x_5558_ = l_List_head_x3f___redArg(v_r_5557_);
                    return v___x_5558_;
                } else {
                    v_val_5559_ = lean_ctor_get(v_c_5555_, 0);
                    v_isSharedCheck_5566_ = (!lean_is_exclusive(v_c_5555_)) as u8;
                    if v_isSharedCheck_5566_ == 0 {
                        v___x_5561_ = v_c_5555_;
                        v_isShared_5562_ = v_isSharedCheck_5566_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5559_);
                        lean_dec(v_c_5555_);
                        v___x_5561_ = lean_box(0);
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
                    v_reuseFailAlloc_5565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_val_5559_);
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
    mut v_x_5567_: *mut LeanObject,
    mut v_c_5568_: *mut LeanObject,
    mut v_x_5569_: *mut LeanObject,
    mut v_r_5570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5571_: *mut LeanObject = core::ptr::null_mut();
    v_res_5571_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___lam__0(
        v_x_5567_, v_c_5568_, v_x_5569_, v_r_5570_,
    );
    lean_dec(v_r_5570_);
    lean_dec(v_x_5567_);
    return v_res_5571_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(
    mut v_inst_5573_: *mut LeanObject,
    mut v_k_5574_: *mut LeanObject,
    mut v_t_5575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    v___f_5576_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg___closed__0;
    v___x_5577_ = lean_apply_1(v_inst_5573_, v_k_5574_);
    v___x_5578_ =
        l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___x_5577_, v_t_5575_, v___f_5576_);
    return v___x_5578_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098(
    mut v_00_u03b1_5579_: *mut LeanObject,
    mut v_00_u03b2_5580_: *mut LeanObject,
    mut v_inst_5581_: *mut LeanObject,
    mut v_k_5582_: *mut LeanObject,
    mut v_t_5583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    v___x_5584_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098___redArg(
        v_inst_5581_,
        v_k_5582_,
        v_t_5583_,
    );
    return v___x_5584_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(
    mut v_x_5585_: *mut LeanObject,
    mut v_x_5586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5597_: u8 = 0;
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_5586_) {
                0 => {
                    v_a_5587_ = lean_ctor_get(v_x_5586_, 0);
                    lean_inc(v_a_5587_);
                    v_a_5588_ = lean_ctor_get(v_x_5586_, 1);
                    lean_inc(v_a_5588_);
                    lean_dec_ref_known(v_x_5586_, 3);
                    v___x_5589_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5589_, 0, v_a_5587_);
                    lean_ctor_set(v___x_5589_, 1, v_a_5588_);
                    v___x_5590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5590_, 0, v___x_5589_);
                    return v___x_5590_;
                }
                1 => {
                    v_a_5591_ = lean_ctor_get(v_x_5586_, 1);
                    lean_inc(v_a_5591_);
                    if lean_obj_tag(v_a_5591_) == 0 {
                        v_a_5592_ = lean_ctor_get(v_x_5586_, 2);
                        lean_inc(v_a_5592_);
                        lean_dec_ref_known(v_x_5586_, 3);
                        v___x_5593_ = l_List_head_x3f___redArg(v_a_5592_);
                        lean_dec(v_a_5592_);
                        if lean_obj_tag(v___x_5593_) == 0 {
                            lean_inc(v_x_5585_);
                            return v_x_5585_;
                        } else {
                            return v___x_5593_;
                        }
                    } else {
                        lean_dec_ref_known(v_x_5586_, 3);
                        v_val_5594_ = lean_ctor_get(v_a_5591_, 0);
                        v_isSharedCheck_5601_ = (!lean_is_exclusive(v_a_5591_)) as u8;
                        if v_isSharedCheck_5601_ == 0 {
                            v___x_5596_ = v_a_5591_;
                            v_isShared_5597_ = v_isSharedCheck_5601_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_5594_);
                            lean_dec(v_a_5591_);
                            v___x_5596_ = lean_box(0);
                            v_isShared_5597_ = v_isSharedCheck_5601_;
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    lean_dec_ref_known(v_x_5586_, 3);
                    lean_inc(v_x_5585_);
                    return v_x_5585_;
                }
            },
            1 => {
                if v_isShared_5597_ == 0 {
                    v___x_5599_ = v___x_5596_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5600_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_val_5594_);
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
    mut v_x_5602_: *mut LeanObject,
    mut v_x_5603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5604_: *mut LeanObject = core::ptr::null_mut();
    v_res_5604_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___lam__0(
        v_x_5602_, v_x_5603_,
    );
    lean_dec(v_x_5602_);
    return v_res_5604_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(
    mut v_inst_5606_: *mut LeanObject,
    mut v_k_5607_: *mut LeanObject,
    mut v_t_5608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    v___f_5609_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg___closed__0;
    v___x_5610_ = lean_apply_1(v_inst_5606_, v_k_5607_);
    v___x_5611_ = lean_box(0);
    v___x_5612_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(
        v___x_5610_,
        v___x_5611_,
        v___f_5609_,
        v_t_5608_,
    );
    return v___x_5612_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27(
    mut v_00_u03b1_5613_: *mut LeanObject,
    mut v_00_u03b2_5614_: *mut LeanObject,
    mut v_inst_5615_: *mut LeanObject,
    mut v_k_5616_: *mut LeanObject,
    mut v_t_5617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    v___x_5618_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27___redArg(
        v_inst_5615_,
        v_k_5616_,
        v_t_5617_,
    );
    return v___x_5618_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___redArg(
    mut v_x_5619_: *mut LeanObject,
    mut v_x_5620_: *mut LeanObject,
    mut v_h__1_5621_: *mut LeanObject,
    mut v_h__2_5622_: *mut LeanObject,
    mut v_h__3_5623_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_5620_) {
        0 => {
            let mut v_a_5624_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5626_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5623_);
            lean_dec(v_h__2_5622_);
            v_a_5624_ = lean_ctor_get(v_x_5620_, 0);
            lean_inc(v_a_5624_);
            v_a_5625_ = lean_ctor_get(v_x_5620_, 1);
            lean_inc(v_a_5625_);
            v_a_5626_ = lean_ctor_get(v_x_5620_, 2);
            lean_inc(v_a_5626_);
            lean_dec_ref_known(v_x_5620_, 3);
            v___x_5627_ = lean_apply_5(
                v_h__1_5621_,
                v_x_5619_,
                v_a_5624_,
                lean_box(0),
                v_a_5625_,
                v_a_5626_,
            );
            return v___x_5627_;
        }
        1 => {
            let mut v_a_5628_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5629_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5630_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5623_);
            lean_dec(v_h__1_5621_);
            v_a_5628_ = lean_ctor_get(v_x_5620_, 0);
            lean_inc(v_a_5628_);
            v_a_5629_ = lean_ctor_get(v_x_5620_, 1);
            lean_inc(v_a_5629_);
            v_a_5630_ = lean_ctor_get(v_x_5620_, 2);
            lean_inc(v_a_5630_);
            lean_dec_ref_known(v_x_5620_, 3);
            v___x_5631_ = lean_apply_4(v_h__2_5622_, v_x_5619_, v_a_5628_, v_a_5629_, v_a_5630_);
            return v___x_5631_;
        }
        _ => {
            let mut v_a_5632_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5633_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5634_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5622_);
            lean_dec(v_h__1_5621_);
            v_a_5632_ = lean_ctor_get(v_x_5620_, 0);
            lean_inc(v_a_5632_);
            v_a_5633_ = lean_ctor_get(v_x_5620_, 1);
            lean_inc(v_a_5633_);
            v_a_5634_ = lean_ctor_get(v_x_5620_, 2);
            lean_inc(v_a_5634_);
            lean_dec_ref_known(v_x_5620_, 3);
            v___x_5635_ = lean_apply_5(
                v_h__3_5623_,
                v_x_5619_,
                v_a_5632_,
                v_a_5633_,
                lean_box(0),
                v_a_5634_,
            );
            return v___x_5635_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(
    mut v_00_u03b1_5636_: *mut LeanObject,
    mut v_00_u03b2_5637_: *mut LeanObject,
    mut v_inst_5638_: *mut LeanObject,
    mut v_k_5639_: *mut LeanObject,
    mut v_motive_5640_: *mut LeanObject,
    mut v_x_5641_: *mut LeanObject,
    mut v_x_5642_: *mut LeanObject,
    mut v_h__1_5643_: *mut LeanObject,
    mut v_h__2_5644_: *mut LeanObject,
    mut v_h__3_5645_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_5642_) {
        0 => {
            let mut v_a_5646_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5647_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5648_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5645_);
            lean_dec(v_h__2_5644_);
            v_a_5646_ = lean_ctor_get(v_x_5642_, 0);
            lean_inc(v_a_5646_);
            v_a_5647_ = lean_ctor_get(v_x_5642_, 1);
            lean_inc(v_a_5647_);
            v_a_5648_ = lean_ctor_get(v_x_5642_, 2);
            lean_inc(v_a_5648_);
            lean_dec_ref_known(v_x_5642_, 3);
            v___x_5649_ = lean_apply_5(
                v_h__1_5643_,
                v_x_5641_,
                v_a_5646_,
                lean_box(0),
                v_a_5647_,
                v_a_5648_,
            );
            return v___x_5649_;
        }
        1 => {
            let mut v_a_5650_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5651_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5652_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5645_);
            lean_dec(v_h__1_5643_);
            v_a_5650_ = lean_ctor_get(v_x_5642_, 0);
            lean_inc(v_a_5650_);
            v_a_5651_ = lean_ctor_get(v_x_5642_, 1);
            lean_inc(v_a_5651_);
            v_a_5652_ = lean_ctor_get(v_x_5642_, 2);
            lean_inc(v_a_5652_);
            lean_dec_ref_known(v_x_5642_, 3);
            v___x_5653_ = lean_apply_4(v_h__2_5644_, v_x_5641_, v_a_5650_, v_a_5651_, v_a_5652_);
            return v___x_5653_;
        }
        _ => {
            let mut v_a_5654_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5655_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5656_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5644_);
            lean_dec(v_h__1_5643_);
            v_a_5654_ = lean_ctor_get(v_x_5642_, 0);
            lean_inc(v_a_5654_);
            v_a_5655_ = lean_ctor_get(v_x_5642_, 1);
            lean_inc(v_a_5655_);
            v_a_5656_ = lean_ctor_get(v_x_5642_, 2);
            lean_inc(v_a_5656_);
            lean_dec_ref_known(v_x_5642_, 3);
            v___x_5657_ = lean_apply_5(
                v_h__3_5645_,
                v_x_5641_,
                v_a_5654_,
                v_a_5655_,
                lean_box(0),
                v_a_5656_,
            );
            return v___x_5657_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter___boxed(
    mut v_00_u03b1_5658_: *mut LeanObject,
    mut v_00_u03b2_5659_: *mut LeanObject,
    mut v_inst_5660_: *mut LeanObject,
    mut v_k_5661_: *mut LeanObject,
    mut v_motive_5662_: *mut LeanObject,
    mut v_x_5663_: *mut LeanObject,
    mut v_x_5664_: *mut LeanObject,
    mut v_h__1_5665_: *mut LeanObject,
    mut v_h__2_5666_: *mut LeanObject,
    mut v_h__3_5667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5668_: *mut LeanObject = core::ptr::null_mut();
    v_res_5668_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_x3f_u2098_x27_match__1_splitter(v_00_u03b1_5658_, v_00_u03b2_5659_, v_inst_5660_, v_k_5661_, v_motive_5662_, v_x_5663_, v_x_5664_, v_h__1_5665_, v_h__2_5666_, v_h__3_5667_);
    lean_dec(v_k_5661_);
    lean_dec_ref(v_inst_5660_);
    return v_res_5668_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(
    mut v_inst_5669_: *mut LeanObject,
    mut v_k_5670_: *mut LeanObject,
    mut v_k_x27_5671_: *mut LeanObject,
) -> u8 {
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: u8 = 0;
    v___x_5672_ = lean_apply_2(v_inst_5669_, v_k_5670_, v_k_x27_5671_);
    v___x_5673_ = (lean_unbox(v___x_5672_) as u8);
    if v___x_5673_ == 1 {
        let mut v___x_5674_: u8 = 0;
        v___x_5674_ = 2;
        return v___x_5674_;
    } else {
        let mut v___x_5675_: u8 = 0;
        v___x_5675_ = (lean_unbox(v___x_5672_) as u8);
        return v___x_5675_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed(
    mut v_inst_5676_: *mut LeanObject,
    mut v_k_5677_: *mut LeanObject,
    mut v_k_x27_5678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5679_: u8 = 0;
    let mut v_r_5680_: *mut LeanObject = core::ptr::null_mut();
    v_res_5679_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0(
        v_inst_5676_,
        v_k_5677_,
        v_k_x27_5678_,
    );
    v_r_5680_ = lean_box((v_res_5679_) as usize);
    return v_r_5680_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(
    mut v_inst_5681_: *mut LeanObject,
    mut v_k_5682_: *mut LeanObject,
    mut v_t_5683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    v___f_5684_ = lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5684_, 0, v_inst_5681_);
    lean_closure_set(v___f_5684_, 1, v_k_5682_);
    v___f_5685_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f_u2098___redArg___closed__0;
    v___x_5686_ =
        l_Std_DTreeMap_Internal_Impl_applyPartition___redArg(v___f_5684_, v_t_5683_, v___f_5685_);
    return v___x_5686_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098(
    mut v_00_u03b1_5687_: *mut LeanObject,
    mut v_00_u03b2_5688_: *mut LeanObject,
    mut v_inst_5689_: *mut LeanObject,
    mut v_k_5690_: *mut LeanObject,
    mut v_t_5691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    v___x_5692_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg(
        v_inst_5689_,
        v_k_5690_,
        v_t_5691_,
    );
    return v___x_5692_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(
    mut v_x_5693_: *mut LeanObject,
    mut v_x_5694_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_5694_) {
        0 => {
            let mut v_a_5695_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5696_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
            v_a_5695_ = lean_ctor_get(v_x_5694_, 0);
            v_a_5696_ = lean_ctor_get(v_x_5694_, 1);
            lean_inc(v_a_5696_);
            lean_inc(v_a_5695_);
            v___x_5697_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_5697_, 0, v_a_5695_);
            lean_ctor_set(v___x_5697_, 1, v_a_5696_);
            v___x_5698_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_5698_, 0, v___x_5697_);
            return v___x_5698_;
        }
        1 => {
            let mut v_a_5699_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
            v_a_5699_ = lean_ctor_get(v_x_5694_, 2);
            v___x_5700_ = l_List_head_x3f___redArg(v_a_5699_);
            if lean_obj_tag(v___x_5700_) == 0 {
                lean_inc(v_x_5693_);
                return v_x_5693_;
            } else {
                return v___x_5700_;
            }
        }
        _ => {
            lean_inc(v_x_5693_);
            return v_x_5693_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1___boxed(
    mut v_x_5701_: *mut LeanObject,
    mut v_x_5702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5703_: *mut LeanObject = core::ptr::null_mut();
    v_res_5703_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___lam__1(
        v_x_5701_, v_x_5702_,
    );
    lean_dec_ref(v_x_5702_);
    lean_dec(v_x_5701_);
    return v_res_5703_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(
    mut v_inst_5705_: *mut LeanObject,
    mut v_k_5706_: *mut LeanObject,
    mut v_t_5707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    v___f_5708_ = lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5708_, 0, v_inst_5705_);
    lean_closure_set(v___f_5708_, 1, v_k_5706_);
    v___f_5709_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg___closed__0;
    v___x_5710_ = lean_box(0);
    v___x_5711_ = l_Std_DTreeMap_Internal_Impl_explore___redArg(
        v___f_5708_,
        v___x_5710_,
        v___f_5709_,
        v_t_5707_,
    );
    return v___x_5711_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27(
    mut v_00_u03b1_5712_: *mut LeanObject,
    mut v_00_u03b2_5713_: *mut LeanObject,
    mut v_inst_5714_: *mut LeanObject,
    mut v_k_5715_: *mut LeanObject,
    mut v_t_5716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    v___x_5717_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27___redArg(
        v_inst_5714_,
        v_k_5715_,
        v_t_5716_,
    );
    return v___x_5717_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(
    mut v_x_5718_: u8,
    mut v_h__1_5719_: *mut LeanObject,
    mut v_h__2_5720_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_5718_ == 0 {
        let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5720_);
        v___x_5721_ = lean_box(0);
        v___x_5722_ = lean_apply_1(v_h__1_5719_, v___x_5721_);
        return v___x_5722_;
    } else {
        let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5719_);
        v___x_5723_ = lean_box((v_x_5718_) as usize);
        v___x_5724_ = lean_apply_2(v_h__2_5720_, v___x_5723_, lean_box(0));
        return v___x_5724_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg___boxed(
    mut v_x_5725_: *mut LeanObject,
    mut v_h__1_5726_: *mut LeanObject,
    mut v_h__2_5727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_5728_: u8 = 0;
    let mut v_res_5729_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_5728_ = (lean_unbox(v_x_5725_) as u8);
    v_res_5729_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_5728_, v_h__1_5726_, v_h__2_5727_);
    return v_res_5729_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(
    mut v_motive_5730_: *mut LeanObject,
    mut v_x_5731_: u8,
    mut v_h__1_5732_: *mut LeanObject,
    mut v_h__2_5733_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_5731_ == 0 {
        let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5733_);
        v___x_5734_ = lean_box(0);
        v___x_5735_ = lean_apply_1(v_h__1_5732_, v___x_5734_);
        return v___x_5735_;
    } else {
        let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5732_);
        v___x_5736_ = lean_box((v_x_5731_) as usize);
        v___x_5737_ = lean_apply_2(v_h__2_5733_, v___x_5736_, lean_box(0));
        return v___x_5737_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter___boxed(
    mut v_motive_5738_: *mut LeanObject,
    mut v_x_5739_: *mut LeanObject,
    mut v_h__1_5740_: *mut LeanObject,
    mut v_h__2_5741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_28__boxed_5742_: u8 = 0;
    let mut v_res_5743_: *mut LeanObject = core::ptr::null_mut();
    v_x_28__boxed_5742_ = (lean_unbox(v_x_5739_) as u8);
    v_res_5743_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go_match__1_splitter(v_motive_5738_, v_x_28__boxed_5742_, v_h__1_5740_, v_h__2_5741_);
    return v_res_5743_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___redArg(
    mut v_x_5744_: *mut LeanObject,
    mut v_x_5745_: *mut LeanObject,
    mut v_h__1_5746_: *mut LeanObject,
    mut v_h__2_5747_: *mut LeanObject,
    mut v_h__3_5748_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_5745_) {
        0 => {
            let mut v_a_5749_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5750_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5751_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5748_);
            lean_dec(v_h__2_5747_);
            v_a_5749_ = lean_ctor_get(v_x_5745_, 0);
            lean_inc(v_a_5749_);
            v_a_5750_ = lean_ctor_get(v_x_5745_, 1);
            lean_inc(v_a_5750_);
            v_a_5751_ = lean_ctor_get(v_x_5745_, 2);
            lean_inc(v_a_5751_);
            lean_dec_ref_known(v_x_5745_, 3);
            v___x_5752_ = lean_apply_5(
                v_h__1_5746_,
                v_x_5744_,
                v_a_5749_,
                lean_box(0),
                v_a_5750_,
                v_a_5751_,
            );
            return v___x_5752_;
        }
        1 => {
            let mut v_a_5753_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5754_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5755_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5748_);
            lean_dec(v_h__1_5746_);
            v_a_5753_ = lean_ctor_get(v_x_5745_, 0);
            lean_inc(v_a_5753_);
            v_a_5754_ = lean_ctor_get(v_x_5745_, 1);
            lean_inc(v_a_5754_);
            v_a_5755_ = lean_ctor_get(v_x_5745_, 2);
            lean_inc(v_a_5755_);
            lean_dec_ref_known(v_x_5745_, 3);
            v___x_5756_ = lean_apply_4(v_h__2_5747_, v_x_5744_, v_a_5753_, v_a_5754_, v_a_5755_);
            return v___x_5756_;
        }
        _ => {
            let mut v_a_5757_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5758_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5759_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5747_);
            lean_dec(v_h__1_5746_);
            v_a_5757_ = lean_ctor_get(v_x_5745_, 0);
            lean_inc(v_a_5757_);
            v_a_5758_ = lean_ctor_get(v_x_5745_, 1);
            lean_inc(v_a_5758_);
            v_a_5759_ = lean_ctor_get(v_x_5745_, 2);
            lean_inc(v_a_5759_);
            lean_dec_ref_known(v_x_5745_, 3);
            v___x_5760_ = lean_apply_5(
                v_h__3_5748_,
                v_x_5744_,
                v_a_5757_,
                v_a_5758_,
                lean_box(0),
                v_a_5759_,
            );
            return v___x_5760_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(
    mut v_00_u03b1_5761_: *mut LeanObject,
    mut v_00_u03b2_5762_: *mut LeanObject,
    mut v_inst_5763_: *mut LeanObject,
    mut v_k_5764_: *mut LeanObject,
    mut v_motive_5765_: *mut LeanObject,
    mut v_x_5766_: *mut LeanObject,
    mut v_x_5767_: *mut LeanObject,
    mut v_h__1_5768_: *mut LeanObject,
    mut v_h__2_5769_: *mut LeanObject,
    mut v_h__3_5770_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_5767_) {
        0 => {
            let mut v_a_5771_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5772_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5773_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5770_);
            lean_dec(v_h__2_5769_);
            v_a_5771_ = lean_ctor_get(v_x_5767_, 0);
            lean_inc(v_a_5771_);
            v_a_5772_ = lean_ctor_get(v_x_5767_, 1);
            lean_inc(v_a_5772_);
            v_a_5773_ = lean_ctor_get(v_x_5767_, 2);
            lean_inc(v_a_5773_);
            lean_dec_ref_known(v_x_5767_, 3);
            v___x_5774_ = lean_apply_5(
                v_h__1_5768_,
                v_x_5766_,
                v_a_5771_,
                lean_box(0),
                v_a_5772_,
                v_a_5773_,
            );
            return v___x_5774_;
        }
        1 => {
            let mut v_a_5775_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5776_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5770_);
            lean_dec(v_h__1_5768_);
            v_a_5775_ = lean_ctor_get(v_x_5767_, 0);
            lean_inc(v_a_5775_);
            v_a_5776_ = lean_ctor_get(v_x_5767_, 1);
            lean_inc(v_a_5776_);
            v_a_5777_ = lean_ctor_get(v_x_5767_, 2);
            lean_inc(v_a_5777_);
            lean_dec_ref_known(v_x_5767_, 3);
            v___x_5778_ = lean_apply_4(v_h__2_5769_, v_x_5766_, v_a_5775_, v_a_5776_, v_a_5777_);
            return v___x_5778_;
        }
        _ => {
            let mut v_a_5779_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5780_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5781_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5769_);
            lean_dec(v_h__1_5768_);
            v_a_5779_ = lean_ctor_get(v_x_5767_, 0);
            lean_inc(v_a_5779_);
            v_a_5780_ = lean_ctor_get(v_x_5767_, 1);
            lean_inc(v_a_5780_);
            v_a_5781_ = lean_ctor_get(v_x_5767_, 2);
            lean_inc(v_a_5781_);
            lean_dec_ref_known(v_x_5767_, 3);
            v___x_5782_ = lean_apply_5(
                v_h__3_5770_,
                v_x_5766_,
                v_a_5779_,
                v_a_5780_,
                lean_box(0),
                v_a_5781_,
            );
            return v___x_5782_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter___boxed(
    mut v_00_u03b1_5783_: *mut LeanObject,
    mut v_00_u03b2_5784_: *mut LeanObject,
    mut v_inst_5785_: *mut LeanObject,
    mut v_k_5786_: *mut LeanObject,
    mut v_motive_5787_: *mut LeanObject,
    mut v_x_5788_: *mut LeanObject,
    mut v_x_5789_: *mut LeanObject,
    mut v_h__1_5790_: *mut LeanObject,
    mut v_h__2_5791_: *mut LeanObject,
    mut v_h__3_5792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5793_: *mut LeanObject = core::ptr::null_mut();
    v_res_5793_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_x3f_u2098_x27_match__1_splitter(v_00_u03b1_5783_, v_00_u03b2_5784_, v_inst_5785_, v_k_5786_, v_motive_5787_, v_x_5788_, v_x_5789_, v_h__1_5790_, v_h__2_5791_, v_h__3_5792_);
    lean_dec(v_k_5786_);
    lean_dec_ref(v_inst_5785_);
    return v_res_5793_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(
    mut v_x_5794_: u8,
    mut v_h__1_5795_: *mut LeanObject,
    mut v_h__2_5796_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_5794_ == 2 {
        let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5796_);
        v___x_5797_ = lean_box(0);
        v___x_5798_ = lean_apply_1(v_h__1_5795_, v___x_5797_);
        return v___x_5798_;
    } else {
        let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5795_);
        v___x_5799_ = lean_box((v_x_5794_) as usize);
        v___x_5800_ = lean_apply_2(v_h__2_5796_, v___x_5799_, lean_box(0));
        return v___x_5800_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg___boxed(
    mut v_x_5801_: *mut LeanObject,
    mut v_h__1_5802_: *mut LeanObject,
    mut v_h__2_5803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_5804_: u8 = 0;
    let mut v_res_5805_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_5804_ = (lean_unbox(v_x_5801_) as u8);
    v_res_5805_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___redArg(v_x_17__boxed_5804_, v_h__1_5802_, v_h__2_5803_);
    return v_res_5805_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(
    mut v_motive_5806_: *mut LeanObject,
    mut v_x_5807_: u8,
    mut v_h__1_5808_: *mut LeanObject,
    mut v_h__2_5809_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_5807_ == 2 {
        let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5809_);
        v___x_5810_ = lean_box(0);
        v___x_5811_ = lean_apply_1(v_h__1_5808_, v___x_5810_);
        return v___x_5811_;
    } else {
        let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5808_);
        v___x_5812_ = lean_box((v_x_5807_) as usize);
        v___x_5813_ = lean_apply_2(v_h__2_5809_, v___x_5812_, lean_box(0));
        return v___x_5813_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter___boxed(
    mut v_motive_5814_: *mut LeanObject,
    mut v_x_5815_: *mut LeanObject,
    mut v_h__1_5816_: *mut LeanObject,
    mut v_h__2_5817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_28__boxed_5818_: u8 = 0;
    let mut v_res_5819_: *mut LeanObject = core::ptr::null_mut();
    v_x_28__boxed_5818_ = (lean_unbox(v_x_5815_) as u8);
    v_res_5819_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go_match__1_splitter(v_motive_5814_, v_x_28__boxed_5818_, v_h__1_5816_, v_h__2_5817_);
    return v_res_5819_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg(
    mut v_x_5820_: u8,
    mut v_h__1_5821_: *mut LeanObject,
    mut v_h__2_5822_: *mut LeanObject,
    mut v_h__3_5823_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5820_ {
        0 => {
            let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5823_);
            lean_dec(v_h__2_5822_);
            v___x_5824_ = lean_box(0);
            v___x_5825_ = lean_apply_1(v_h__1_5821_, v___x_5824_);
            return v___x_5825_;
        }
        1 => {
            let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5823_);
            lean_dec(v_h__1_5821_);
            v___x_5826_ = lean_box(0);
            v___x_5827_ = lean_apply_1(v_h__2_5822_, v___x_5826_);
            return v___x_5827_;
        }
        _ => {
            let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5822_);
            lean_dec(v_h__1_5821_);
            v___x_5828_ = lean_box(0);
            v___x_5829_ = lean_apply_1(v_h__3_5823_, v___x_5828_);
            return v___x_5829_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___redArg___boxed(
    mut v_x_5830_: *mut LeanObject,
    mut v_h__1_5831_: *mut LeanObject,
    mut v_h__2_5832_: *mut LeanObject,
    mut v_h__3_5833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_5834_: u8 = 0;
    let mut v_res_5835_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_5834_ = (lean_unbox(v_x_5830_) as u8);
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
    mut v_motive_5836_: *mut LeanObject,
    mut v_x_5837_: u8,
    mut v_h__1_5838_: *mut LeanObject,
    mut v_h__2_5839_: *mut LeanObject,
    mut v_h__3_5840_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5837_ {
        0 => {
            let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5840_);
            lean_dec(v_h__2_5839_);
            v___x_5841_ = lean_box(0);
            v___x_5842_ = lean_apply_1(v_h__1_5838_, v___x_5841_);
            return v___x_5842_;
        }
        1 => {
            let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5840_);
            lean_dec(v_h__1_5838_);
            v___x_5843_ = lean_box(0);
            v___x_5844_ = lean_apply_1(v_h__2_5839_, v___x_5843_);
            return v___x_5844_;
        }
        _ => {
            let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5839_);
            lean_dec(v_h__1_5838_);
            v___x_5845_ = lean_box(0);
            v___x_5846_ = lean_apply_1(v_h__3_5840_, v___x_5845_);
            return v___x_5846_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Ordering_swap_match__1_splitter___boxed(
    mut v_motive_5847_: *mut LeanObject,
    mut v_x_5848_: *mut LeanObject,
    mut v_h__1_5849_: *mut LeanObject,
    mut v_h__2_5850_: *mut LeanObject,
    mut v_h__3_5851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_5852_: u8 = 0;
    let mut v_res_5853_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_5852_ = (lean_unbox(v_x_5848_) as u8);
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
    mut v_x_5854_: *mut LeanObject,
    mut v_h__1_5855_: *mut LeanObject,
    mut v_h__2_5856_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5854_) == 0 {
        let mut v_size_5857_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5858_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5859_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5860_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5855_);
        v_size_5857_ = lean_ctor_get(v_x_5854_, 0);
        lean_inc(v_size_5857_);
        v_k_5858_ = lean_ctor_get(v_x_5854_, 1);
        lean_inc(v_k_5858_);
        v_v_5859_ = lean_ctor_get(v_x_5854_, 2);
        lean_inc(v_v_5859_);
        v_l_5860_ = lean_ctor_get(v_x_5854_, 3);
        lean_inc(v_l_5860_);
        v_r_5861_ = lean_ctor_get(v_x_5854_, 4);
        lean_inc(v_r_5861_);
        lean_dec_ref_known(v_x_5854_, 5);
        v___x_5862_ = lean_apply_7(
            v_h__2_5856_,
            v_size_5857_,
            v_k_5858_,
            v_v_5859_,
            v_l_5860_,
            v_r_5861_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5862_;
    } else {
        let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5856_);
        v___x_5863_ = lean_apply_2(v_h__1_5855_, lean_box(0), lean_box(0));
        return v___x_5863_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(
    mut v_00_u03b1_5864_: *mut LeanObject,
    mut v_00_u03b2_5865_: *mut LeanObject,
    mut v_inst_5866_: *mut LeanObject,
    mut v_k_5867_: *mut LeanObject,
    mut v_motive_5868_: *mut LeanObject,
    mut v_x_5869_: *mut LeanObject,
    mut v_x_5870_: *mut LeanObject,
    mut v_x_5871_: *mut LeanObject,
    mut v_h__1_5872_: *mut LeanObject,
    mut v_h__2_5873_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5869_) == 0 {
        let mut v_size_5874_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5875_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5876_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5877_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5872_);
        v_size_5874_ = lean_ctor_get(v_x_5869_, 0);
        lean_inc(v_size_5874_);
        v_k_5875_ = lean_ctor_get(v_x_5869_, 1);
        lean_inc(v_k_5875_);
        v_v_5876_ = lean_ctor_get(v_x_5869_, 2);
        lean_inc(v_v_5876_);
        v_l_5877_ = lean_ctor_get(v_x_5869_, 3);
        lean_inc(v_l_5877_);
        v_r_5878_ = lean_ctor_get(v_x_5869_, 4);
        lean_inc(v_r_5878_);
        lean_dec_ref_known(v_x_5869_, 5);
        v___x_5879_ = lean_apply_7(
            v_h__2_5873_,
            v_size_5874_,
            v_k_5875_,
            v_v_5876_,
            v_l_5877_,
            v_r_5878_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5879_;
    } else {
        let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5873_);
        v___x_5880_ = lean_apply_2(v_h__1_5872_, lean_box(0), lean_box(0));
        return v___x_5880_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter___boxed(
    mut v_00_u03b1_5881_: *mut LeanObject,
    mut v_00_u03b2_5882_: *mut LeanObject,
    mut v_inst_5883_: *mut LeanObject,
    mut v_k_5884_: *mut LeanObject,
    mut v_motive_5885_: *mut LeanObject,
    mut v_x_5886_: *mut LeanObject,
    mut v_x_5887_: *mut LeanObject,
    mut v_x_5888_: *mut LeanObject,
    mut v_h__1_5889_: *mut LeanObject,
    mut v_h__2_5890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5891_: *mut LeanObject = core::ptr::null_mut();
    v_res_5891_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGE_match__1_splitter(v_00_u03b1_5881_, v_00_u03b2_5882_, v_inst_5883_, v_k_5884_, v_motive_5885_, v_x_5886_, v_x_5887_, v_x_5888_, v_h__1_5889_, v_h__2_5890_);
    lean_dec(v_k_5884_);
    lean_dec_ref(v_inst_5883_);
    return v_res_5891_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___redArg(
    mut v_x_5892_: *mut LeanObject,
    mut v_h__1_5893_: *mut LeanObject,
    mut v_h__2_5894_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5892_) == 0 {
        let mut v_size_5895_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5896_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5897_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5898_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5893_);
        v_size_5895_ = lean_ctor_get(v_x_5892_, 0);
        lean_inc(v_size_5895_);
        v_k_5896_ = lean_ctor_get(v_x_5892_, 1);
        lean_inc(v_k_5896_);
        v_v_5897_ = lean_ctor_get(v_x_5892_, 2);
        lean_inc(v_v_5897_);
        v_l_5898_ = lean_ctor_get(v_x_5892_, 3);
        lean_inc(v_l_5898_);
        v_r_5899_ = lean_ctor_get(v_x_5892_, 4);
        lean_inc(v_r_5899_);
        lean_dec_ref_known(v_x_5892_, 5);
        v___x_5900_ = lean_apply_7(
            v_h__2_5894_,
            v_size_5895_,
            v_k_5896_,
            v_v_5897_,
            v_l_5898_,
            v_r_5899_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5900_;
    } else {
        let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5894_);
        v___x_5901_ = lean_apply_2(v_h__1_5893_, lean_box(0), lean_box(0));
        return v___x_5901_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(
    mut v_00_u03b1_5902_: *mut LeanObject,
    mut v_00_u03b2_5903_: *mut LeanObject,
    mut v_inst_5904_: *mut LeanObject,
    mut v_k_5905_: *mut LeanObject,
    mut v_motive_5906_: *mut LeanObject,
    mut v_x_5907_: *mut LeanObject,
    mut v_x_5908_: *mut LeanObject,
    mut v_x_5909_: *mut LeanObject,
    mut v_h__1_5910_: *mut LeanObject,
    mut v_h__2_5911_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5907_) == 0 {
        let mut v_size_5912_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5913_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5914_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5915_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5910_);
        v_size_5912_ = lean_ctor_get(v_x_5907_, 0);
        lean_inc(v_size_5912_);
        v_k_5913_ = lean_ctor_get(v_x_5907_, 1);
        lean_inc(v_k_5913_);
        v_v_5914_ = lean_ctor_get(v_x_5907_, 2);
        lean_inc(v_v_5914_);
        v_l_5915_ = lean_ctor_get(v_x_5907_, 3);
        lean_inc(v_l_5915_);
        v_r_5916_ = lean_ctor_get(v_x_5907_, 4);
        lean_inc(v_r_5916_);
        lean_dec_ref_known(v_x_5907_, 5);
        v___x_5917_ = lean_apply_7(
            v_h__2_5911_,
            v_size_5912_,
            v_k_5913_,
            v_v_5914_,
            v_l_5915_,
            v_r_5916_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5917_;
    } else {
        let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5911_);
        v___x_5918_ = lean_apply_2(v_h__1_5910_, lean_box(0), lean_box(0));
        return v___x_5918_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter___boxed(
    mut v_00_u03b1_5919_: *mut LeanObject,
    mut v_00_u03b2_5920_: *mut LeanObject,
    mut v_inst_5921_: *mut LeanObject,
    mut v_k_5922_: *mut LeanObject,
    mut v_motive_5923_: *mut LeanObject,
    mut v_x_5924_: *mut LeanObject,
    mut v_x_5925_: *mut LeanObject,
    mut v_x_5926_: *mut LeanObject,
    mut v_h__1_5927_: *mut LeanObject,
    mut v_h__2_5928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5929_: *mut LeanObject = core::ptr::null_mut();
    v_res_5929_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryGT_match__1_splitter(v_00_u03b1_5919_, v_00_u03b2_5920_, v_inst_5921_, v_k_5922_, v_motive_5923_, v_x_5924_, v_x_5925_, v_x_5926_, v_h__1_5927_, v_h__2_5928_);
    lean_dec(v_k_5922_);
    lean_dec_ref(v_inst_5921_);
    return v_res_5929_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___redArg(
    mut v_x_5930_: *mut LeanObject,
    mut v_h__1_5931_: *mut LeanObject,
    mut v_h__2_5932_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5930_) == 0 {
        let mut v_size_5933_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5934_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5935_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5936_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5931_);
        v_size_5933_ = lean_ctor_get(v_x_5930_, 0);
        lean_inc(v_size_5933_);
        v_k_5934_ = lean_ctor_get(v_x_5930_, 1);
        lean_inc(v_k_5934_);
        v_v_5935_ = lean_ctor_get(v_x_5930_, 2);
        lean_inc(v_v_5935_);
        v_l_5936_ = lean_ctor_get(v_x_5930_, 3);
        lean_inc(v_l_5936_);
        v_r_5937_ = lean_ctor_get(v_x_5930_, 4);
        lean_inc(v_r_5937_);
        lean_dec_ref_known(v_x_5930_, 5);
        v___x_5938_ = lean_apply_7(
            v_h__2_5932_,
            v_size_5933_,
            v_k_5934_,
            v_v_5935_,
            v_l_5936_,
            v_r_5937_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5938_;
    } else {
        let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5932_);
        v___x_5939_ = lean_apply_2(v_h__1_5931_, lean_box(0), lean_box(0));
        return v___x_5939_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(
    mut v_00_u03b1_5940_: *mut LeanObject,
    mut v_00_u03b2_5941_: *mut LeanObject,
    mut v_inst_5942_: *mut LeanObject,
    mut v_k_5943_: *mut LeanObject,
    mut v_motive_5944_: *mut LeanObject,
    mut v_x_5945_: *mut LeanObject,
    mut v_x_5946_: *mut LeanObject,
    mut v_x_5947_: *mut LeanObject,
    mut v_h__1_5948_: *mut LeanObject,
    mut v_h__2_5949_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5945_) == 0 {
        let mut v_size_5950_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_5951_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5952_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_5953_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_5954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5948_);
        v_size_5950_ = lean_ctor_get(v_x_5945_, 0);
        lean_inc(v_size_5950_);
        v_k_5951_ = lean_ctor_get(v_x_5945_, 1);
        lean_inc(v_k_5951_);
        v_v_5952_ = lean_ctor_get(v_x_5945_, 2);
        lean_inc(v_v_5952_);
        v_l_5953_ = lean_ctor_get(v_x_5945_, 3);
        lean_inc(v_l_5953_);
        v_r_5954_ = lean_ctor_get(v_x_5945_, 4);
        lean_inc(v_r_5954_);
        lean_dec_ref_known(v_x_5945_, 5);
        v___x_5955_ = lean_apply_7(
            v_h__2_5949_,
            v_size_5950_,
            v_k_5951_,
            v_v_5952_,
            v_l_5953_,
            v_r_5954_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_5955_;
    } else {
        let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5949_);
        v___x_5956_ = lean_apply_2(v_h__1_5948_, lean_box(0), lean_box(0));
        return v___x_5956_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter___boxed(
    mut v_00_u03b1_5957_: *mut LeanObject,
    mut v_00_u03b2_5958_: *mut LeanObject,
    mut v_inst_5959_: *mut LeanObject,
    mut v_k_5960_: *mut LeanObject,
    mut v_motive_5961_: *mut LeanObject,
    mut v_x_5962_: *mut LeanObject,
    mut v_x_5963_: *mut LeanObject,
    mut v_x_5964_: *mut LeanObject,
    mut v_h__1_5965_: *mut LeanObject,
    mut v_h__2_5966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5967_: *mut LeanObject = core::ptr::null_mut();
    v_res_5967_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__3_splitter(v_00_u03b1_5957_, v_00_u03b2_5958_, v_inst_5959_, v_k_5960_, v_motive_5961_, v_x_5962_, v_x_5963_, v_x_5964_, v_h__1_5965_, v_h__2_5966_);
    lean_dec(v_k_5960_);
    lean_dec_ref(v_inst_5959_);
    return v_res_5967_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(
    mut v_x_5968_: u8,
    mut v_h__1_5969_: *mut LeanObject,
    mut v_h__2_5970_: *mut LeanObject,
    mut v_h__3_5971_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5968_ {
        0 => {
            let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5970_);
            lean_dec(v_h__1_5969_);
            v___x_5972_ = lean_apply_1(v_h__3_5971_, lean_box(0));
            return v___x_5972_;
        }
        1 => {
            let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5971_);
            lean_dec(v_h__1_5969_);
            v___x_5973_ = lean_apply_1(v_h__2_5970_, lean_box(0));
            return v___x_5973_;
        }
        _ => {
            let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5971_);
            lean_dec(v_h__2_5970_);
            v___x_5974_ = lean_apply_1(v_h__1_5969_, lean_box(0));
            return v___x_5974_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg___boxed(
    mut v_x_5975_: *mut LeanObject,
    mut v_h__1_5976_: *mut LeanObject,
    mut v_h__2_5977_: *mut LeanObject,
    mut v_h__3_5978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_5979_: u8 = 0;
    let mut v_res_5980_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_5979_ = (lean_unbox(v_x_5975_) as u8);
    v_res_5980_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___redArg(v_x_33__boxed_5979_, v_h__1_5976_, v_h__2_5977_, v_h__3_5978_);
    return v_res_5980_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(
    mut v_motive_5981_: *mut LeanObject,
    mut v_x_5982_: u8,
    mut v_h__1_5983_: *mut LeanObject,
    mut v_h__2_5984_: *mut LeanObject,
    mut v_h__3_5985_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_5982_ {
        0 => {
            let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_5984_);
            lean_dec(v_h__1_5983_);
            v___x_5986_ = lean_apply_1(v_h__3_5985_, lean_box(0));
            return v___x_5986_;
        }
        1 => {
            let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5985_);
            lean_dec(v_h__1_5983_);
            v___x_5987_ = lean_apply_1(v_h__2_5984_, lean_box(0));
            return v___x_5987_;
        }
        _ => {
            let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_5985_);
            lean_dec(v_h__2_5984_);
            v___x_5988_ = lean_apply_1(v_h__1_5983_, lean_box(0));
            return v___x_5988_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter___boxed(
    mut v_motive_5989_: *mut LeanObject,
    mut v_x_5990_: *mut LeanObject,
    mut v_h__1_5991_: *mut LeanObject,
    mut v_h__2_5992_: *mut LeanObject,
    mut v_h__3_5993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_42__boxed_5994_: u8 = 0;
    let mut v_res_5995_: *mut LeanObject = core::ptr::null_mut();
    v_x_42__boxed_5994_ = (lean_unbox(v_x_5990_) as u8);
    v_res_5995_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLE_match__1_splitter(v_motive_5989_, v_x_42__boxed_5994_, v_h__1_5991_, v_h__2_5992_, v_h__3_5993_);
    return v_res_5995_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___redArg(
    mut v_x_5996_: *mut LeanObject,
    mut v_h__1_5997_: *mut LeanObject,
    mut v_h__2_5998_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5996_) == 0 {
        let mut v_size_5999_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6000_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6001_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6002_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5997_);
        v_size_5999_ = lean_ctor_get(v_x_5996_, 0);
        lean_inc(v_size_5999_);
        v_k_6000_ = lean_ctor_get(v_x_5996_, 1);
        lean_inc(v_k_6000_);
        v_v_6001_ = lean_ctor_get(v_x_5996_, 2);
        lean_inc(v_v_6001_);
        v_l_6002_ = lean_ctor_get(v_x_5996_, 3);
        lean_inc(v_l_6002_);
        v_r_6003_ = lean_ctor_get(v_x_5996_, 4);
        lean_inc(v_r_6003_);
        lean_dec_ref_known(v_x_5996_, 5);
        v___x_6004_ = lean_apply_7(
            v_h__2_5998_,
            v_size_5999_,
            v_k_6000_,
            v_v_6001_,
            v_l_6002_,
            v_r_6003_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6004_;
    } else {
        let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5998_);
        v___x_6005_ = lean_apply_2(v_h__1_5997_, lean_box(0), lean_box(0));
        return v___x_6005_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(
    mut v_00_u03b1_6006_: *mut LeanObject,
    mut v_00_u03b2_6007_: *mut LeanObject,
    mut v_inst_6008_: *mut LeanObject,
    mut v_k_6009_: *mut LeanObject,
    mut v_motive_6010_: *mut LeanObject,
    mut v_x_6011_: *mut LeanObject,
    mut v_x_6012_: *mut LeanObject,
    mut v_x_6013_: *mut LeanObject,
    mut v_h__1_6014_: *mut LeanObject,
    mut v_h__2_6015_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6011_) == 0 {
        let mut v_size_6016_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6017_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6018_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6019_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6020_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6014_);
        v_size_6016_ = lean_ctor_get(v_x_6011_, 0);
        lean_inc(v_size_6016_);
        v_k_6017_ = lean_ctor_get(v_x_6011_, 1);
        lean_inc(v_k_6017_);
        v_v_6018_ = lean_ctor_get(v_x_6011_, 2);
        lean_inc(v_v_6018_);
        v_l_6019_ = lean_ctor_get(v_x_6011_, 3);
        lean_inc(v_l_6019_);
        v_r_6020_ = lean_ctor_get(v_x_6011_, 4);
        lean_inc(v_r_6020_);
        lean_dec_ref_known(v_x_6011_, 5);
        v___x_6021_ = lean_apply_7(
            v_h__2_6015_,
            v_size_6016_,
            v_k_6017_,
            v_v_6018_,
            v_l_6019_,
            v_r_6020_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6021_;
    } else {
        let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6015_);
        v___x_6022_ = lean_apply_2(v_h__1_6014_, lean_box(0), lean_box(0));
        return v___x_6022_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter___boxed(
    mut v_00_u03b1_6023_: *mut LeanObject,
    mut v_00_u03b2_6024_: *mut LeanObject,
    mut v_inst_6025_: *mut LeanObject,
    mut v_k_6026_: *mut LeanObject,
    mut v_motive_6027_: *mut LeanObject,
    mut v_x_6028_: *mut LeanObject,
    mut v_x_6029_: *mut LeanObject,
    mut v_x_6030_: *mut LeanObject,
    mut v_h__1_6031_: *mut LeanObject,
    mut v_h__2_6032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6033_: *mut LeanObject = core::ptr::null_mut();
    v_res_6033_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_getEntryLT_match__1_splitter(v_00_u03b1_6023_, v_00_u03b2_6024_, v_inst_6025_, v_k_6026_, v_motive_6027_, v_x_6028_, v_x_6029_, v_x_6030_, v_h__1_6031_, v_h__2_6032_);
    lean_dec(v_k_6026_);
    lean_dec_ref(v_inst_6025_);
    return v_res_6033_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter___redArg(
    mut v_x_6034_: *mut LeanObject,
    mut v_x_6035_: *mut LeanObject,
    mut v_h__1_6036_: *mut LeanObject,
    mut v_h__2_6037_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6034_) == 0 {
        let mut v_size_6038_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6039_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6040_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6041_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6036_);
        v_size_6038_ = lean_ctor_get(v_x_6034_, 0);
        lean_inc(v_size_6038_);
        v_k_6039_ = lean_ctor_get(v_x_6034_, 1);
        lean_inc(v_k_6039_);
        v_v_6040_ = lean_ctor_get(v_x_6034_, 2);
        lean_inc(v_v_6040_);
        v_l_6041_ = lean_ctor_get(v_x_6034_, 3);
        lean_inc(v_l_6041_);
        v_r_6042_ = lean_ctor_get(v_x_6034_, 4);
        lean_inc(v_r_6042_);
        lean_dec_ref_known(v_x_6034_, 5);
        v___x_6043_ = lean_apply_6(
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
        let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6037_);
        v___x_6044_ = lean_apply_1(v_h__1_6036_, v_x_6035_);
        return v___x_6044_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f_match__1_splitter(
    mut v_00_u03b1_6045_: *mut LeanObject,
    mut v_00_u03b2_6046_: *mut LeanObject,
    mut v_motive_6047_: *mut LeanObject,
    mut v_x_6048_: *mut LeanObject,
    mut v_x_6049_: *mut LeanObject,
    mut v_h__1_6050_: *mut LeanObject,
    mut v_h__2_6051_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6048_) == 0 {
        let mut v_size_6052_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6053_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6054_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6055_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6050_);
        v_size_6052_ = lean_ctor_get(v_x_6048_, 0);
        lean_inc(v_size_6052_);
        v_k_6053_ = lean_ctor_get(v_x_6048_, 1);
        lean_inc(v_k_6053_);
        v_v_6054_ = lean_ctor_get(v_x_6048_, 2);
        lean_inc(v_v_6054_);
        v_l_6055_ = lean_ctor_get(v_x_6048_, 3);
        lean_inc(v_l_6055_);
        v_r_6056_ = lean_ctor_get(v_x_6048_, 4);
        lean_inc(v_r_6056_);
        lean_dec_ref_known(v_x_6048_, 5);
        v___x_6057_ = lean_apply_6(
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
        let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6051_);
        v___x_6058_ = lean_apply_1(v_h__1_6050_, v_x_6049_);
        return v___x_6058_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter___redArg(
    mut v_x_6059_: *mut LeanObject,
    mut v_x_6060_: *mut LeanObject,
    mut v_h__1_6061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    v_size_6062_ = lean_ctor_get(v_x_6059_, 0);
    lean_inc(v_size_6062_);
    v_k_6063_ = lean_ctor_get(v_x_6059_, 1);
    lean_inc(v_k_6063_);
    v_v_6064_ = lean_ctor_get(v_x_6059_, 2);
    lean_inc(v_v_6064_);
    v_l_6065_ = lean_ctor_get(v_x_6059_, 3);
    lean_inc(v_l_6065_);
    v_r_6066_ = lean_ctor_get(v_x_6059_, 4);
    lean_inc(v_r_6066_);
    lean_dec(v_x_6059_);
    v___x_6067_ = lean_apply_8(
        v_h__1_6061_,
        v_size_6062_,
        v_k_6063_,
        v_v_6064_,
        v_l_6065_,
        v_r_6066_,
        lean_box(0),
        v_x_6060_,
        lean_box(0),
    );
    return v___x_6067_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdx_match__1_splitter(
    mut v_00_u03b1_6068_: *mut LeanObject,
    mut v_00_u03b2_6069_: *mut LeanObject,
    mut v_motive_6070_: *mut LeanObject,
    mut v_x_6071_: *mut LeanObject,
    mut v_x_6072_: *mut LeanObject,
    mut v_x_6073_: *mut LeanObject,
    mut v_x_6074_: *mut LeanObject,
    mut v_h__1_6075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    v_size_6076_ = lean_ctor_get(v_x_6071_, 0);
    lean_inc(v_size_6076_);
    v_k_6077_ = lean_ctor_get(v_x_6071_, 1);
    lean_inc(v_k_6077_);
    v_v_6078_ = lean_ctor_get(v_x_6071_, 2);
    lean_inc(v_v_6078_);
    v_l_6079_ = lean_ctor_get(v_x_6071_, 3);
    lean_inc(v_l_6079_);
    v_r_6080_ = lean_ctor_get(v_x_6071_, 4);
    lean_inc(v_r_6080_);
    lean_dec(v_x_6071_);
    v___x_6081_ = lean_apply_8(
        v_h__1_6075_,
        v_size_6076_,
        v_k_6077_,
        v_v_6078_,
        v_l_6079_,
        v_r_6080_,
        lean_box(0),
        v_x_6073_,
        lean_box(0),
    );
    return v___x_6081_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter___redArg(
    mut v_x_6082_: *mut LeanObject,
    mut v_x_6083_: *mut LeanObject,
    mut v_x_6084_: *mut LeanObject,
    mut v_h__1_6085_: *mut LeanObject,
    mut v_h__2_6086_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6082_) == 0 {
        let mut v_size_6087_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6088_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6089_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6090_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6085_);
        v_size_6087_ = lean_ctor_get(v_x_6082_, 0);
        lean_inc(v_size_6087_);
        v_k_6088_ = lean_ctor_get(v_x_6082_, 1);
        lean_inc(v_k_6088_);
        v_v_6089_ = lean_ctor_get(v_x_6082_, 2);
        lean_inc(v_v_6089_);
        v_l_6090_ = lean_ctor_get(v_x_6082_, 3);
        lean_inc(v_l_6090_);
        v_r_6091_ = lean_ctor_get(v_x_6082_, 4);
        lean_inc(v_r_6091_);
        lean_dec_ref_known(v_x_6082_, 5);
        v___x_6092_ = lean_apply_7(
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
        let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6086_);
        v___x_6093_ = lean_apply_2(v_h__1_6085_, v_x_6083_, v_x_6084_);
        return v___x_6093_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_entryAtIdxD_match__1_splitter(
    mut v_00_u03b1_6094_: *mut LeanObject,
    mut v_00_u03b2_6095_: *mut LeanObject,
    mut v_motive_6096_: *mut LeanObject,
    mut v_x_6097_: *mut LeanObject,
    mut v_x_6098_: *mut LeanObject,
    mut v_x_6099_: *mut LeanObject,
    mut v_h__1_6100_: *mut LeanObject,
    mut v_h__2_6101_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6097_) == 0 {
        let mut v_size_6102_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6103_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6104_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6105_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6100_);
        v_size_6102_ = lean_ctor_get(v_x_6097_, 0);
        lean_inc(v_size_6102_);
        v_k_6103_ = lean_ctor_get(v_x_6097_, 1);
        lean_inc(v_k_6103_);
        v_v_6104_ = lean_ctor_get(v_x_6097_, 2);
        lean_inc(v_v_6104_);
        v_l_6105_ = lean_ctor_get(v_x_6097_, 3);
        lean_inc(v_l_6105_);
        v_r_6106_ = lean_ctor_get(v_x_6097_, 4);
        lean_inc(v_r_6106_);
        lean_dec_ref_known(v_x_6097_, 5);
        v___x_6107_ = lean_apply_7(
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
        let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6101_);
        v___x_6108_ = lean_apply_2(v_h__1_6100_, v_x_6098_, v_x_6099_);
        return v___x_6108_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___redArg(
    mut v_x_6109_: *mut LeanObject,
    mut v_h__1_6110_: *mut LeanObject,
    mut v_h__2_6111_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6109_) == 0 {
        let mut v_size_6112_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6113_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6114_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6115_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6110_);
        v_size_6112_ = lean_ctor_get(v_x_6109_, 0);
        lean_inc(v_size_6112_);
        v_k_6113_ = lean_ctor_get(v_x_6109_, 1);
        lean_inc(v_k_6113_);
        v_v_6114_ = lean_ctor_get(v_x_6109_, 2);
        lean_inc(v_v_6114_);
        v_l_6115_ = lean_ctor_get(v_x_6109_, 3);
        lean_inc(v_l_6115_);
        v_r_6116_ = lean_ctor_get(v_x_6109_, 4);
        lean_inc(v_r_6116_);
        lean_dec_ref_known(v_x_6109_, 5);
        v___x_6117_ = lean_apply_7(
            v_h__2_6111_,
            v_size_6112_,
            v_k_6113_,
            v_v_6114_,
            v_l_6115_,
            v_r_6116_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6117_;
    } else {
        let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6111_);
        v___x_6118_ = lean_apply_2(v_h__1_6110_, lean_box(0), lean_box(0));
        return v___x_6118_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(
    mut v_00_u03b1_6119_: *mut LeanObject,
    mut v_00_u03b2_6120_: *mut LeanObject,
    mut v_inst_6121_: *mut LeanObject,
    mut v_k_6122_: *mut LeanObject,
    mut v_motive_6123_: *mut LeanObject,
    mut v_x_6124_: *mut LeanObject,
    mut v_x_6125_: *mut LeanObject,
    mut v_x_6126_: *mut LeanObject,
    mut v_h__1_6127_: *mut LeanObject,
    mut v_h__2_6128_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6124_) == 0 {
        let mut v_size_6129_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6130_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6131_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6132_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6127_);
        v_size_6129_ = lean_ctor_get(v_x_6124_, 0);
        lean_inc(v_size_6129_);
        v_k_6130_ = lean_ctor_get(v_x_6124_, 1);
        lean_inc(v_k_6130_);
        v_v_6131_ = lean_ctor_get(v_x_6124_, 2);
        lean_inc(v_v_6131_);
        v_l_6132_ = lean_ctor_get(v_x_6124_, 3);
        lean_inc(v_l_6132_);
        v_r_6133_ = lean_ctor_get(v_x_6124_, 4);
        lean_inc(v_r_6133_);
        lean_dec_ref_known(v_x_6124_, 5);
        v___x_6134_ = lean_apply_7(
            v_h__2_6128_,
            v_size_6129_,
            v_k_6130_,
            v_v_6131_,
            v_l_6132_,
            v_r_6133_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6134_;
    } else {
        let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6128_);
        v___x_6135_ = lean_apply_2(v_h__1_6127_, lean_box(0), lean_box(0));
        return v___x_6135_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter___boxed(
    mut v_00_u03b1_6136_: *mut LeanObject,
    mut v_00_u03b2_6137_: *mut LeanObject,
    mut v_inst_6138_: *mut LeanObject,
    mut v_k_6139_: *mut LeanObject,
    mut v_motive_6140_: *mut LeanObject,
    mut v_x_6141_: *mut LeanObject,
    mut v_x_6142_: *mut LeanObject,
    mut v_x_6143_: *mut LeanObject,
    mut v_h__1_6144_: *mut LeanObject,
    mut v_h__2_6145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6146_: *mut LeanObject = core::ptr::null_mut();
    v_res_6146_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGE_match__1_splitter(v_00_u03b1_6136_, v_00_u03b2_6137_, v_inst_6138_, v_k_6139_, v_motive_6140_, v_x_6141_, v_x_6142_, v_x_6143_, v_h__1_6144_, v_h__2_6145_);
    lean_dec(v_k_6139_);
    lean_dec_ref(v_inst_6138_);
    return v_res_6146_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___redArg(
    mut v_x_6147_: *mut LeanObject,
    mut v_h__1_6148_: *mut LeanObject,
    mut v_h__2_6149_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6147_) == 0 {
        let mut v_size_6150_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6151_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6152_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6153_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6148_);
        v_size_6150_ = lean_ctor_get(v_x_6147_, 0);
        lean_inc(v_size_6150_);
        v_k_6151_ = lean_ctor_get(v_x_6147_, 1);
        lean_inc(v_k_6151_);
        v_v_6152_ = lean_ctor_get(v_x_6147_, 2);
        lean_inc(v_v_6152_);
        v_l_6153_ = lean_ctor_get(v_x_6147_, 3);
        lean_inc(v_l_6153_);
        v_r_6154_ = lean_ctor_get(v_x_6147_, 4);
        lean_inc(v_r_6154_);
        lean_dec_ref_known(v_x_6147_, 5);
        v___x_6155_ = lean_apply_7(
            v_h__2_6149_,
            v_size_6150_,
            v_k_6151_,
            v_v_6152_,
            v_l_6153_,
            v_r_6154_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6155_;
    } else {
        let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6149_);
        v___x_6156_ = lean_apply_2(v_h__1_6148_, lean_box(0), lean_box(0));
        return v___x_6156_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(
    mut v_00_u03b1_6157_: *mut LeanObject,
    mut v_00_u03b2_6158_: *mut LeanObject,
    mut v_inst_6159_: *mut LeanObject,
    mut v_k_6160_: *mut LeanObject,
    mut v_motive_6161_: *mut LeanObject,
    mut v_x_6162_: *mut LeanObject,
    mut v_x_6163_: *mut LeanObject,
    mut v_x_6164_: *mut LeanObject,
    mut v_h__1_6165_: *mut LeanObject,
    mut v_h__2_6166_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6162_) == 0 {
        let mut v_size_6167_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6168_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6169_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6165_);
        v_size_6167_ = lean_ctor_get(v_x_6162_, 0);
        lean_inc(v_size_6167_);
        v_k_6168_ = lean_ctor_get(v_x_6162_, 1);
        lean_inc(v_k_6168_);
        v_v_6169_ = lean_ctor_get(v_x_6162_, 2);
        lean_inc(v_v_6169_);
        v_l_6170_ = lean_ctor_get(v_x_6162_, 3);
        lean_inc(v_l_6170_);
        v_r_6171_ = lean_ctor_get(v_x_6162_, 4);
        lean_inc(v_r_6171_);
        lean_dec_ref_known(v_x_6162_, 5);
        v___x_6172_ = lean_apply_7(
            v_h__2_6166_,
            v_size_6167_,
            v_k_6168_,
            v_v_6169_,
            v_l_6170_,
            v_r_6171_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6172_;
    } else {
        let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6166_);
        v___x_6173_ = lean_apply_2(v_h__1_6165_, lean_box(0), lean_box(0));
        return v___x_6173_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter___boxed(
    mut v_00_u03b1_6174_: *mut LeanObject,
    mut v_00_u03b2_6175_: *mut LeanObject,
    mut v_inst_6176_: *mut LeanObject,
    mut v_k_6177_: *mut LeanObject,
    mut v_motive_6178_: *mut LeanObject,
    mut v_x_6179_: *mut LeanObject,
    mut v_x_6180_: *mut LeanObject,
    mut v_x_6181_: *mut LeanObject,
    mut v_h__1_6182_: *mut LeanObject,
    mut v_h__2_6183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6184_: *mut LeanObject = core::ptr::null_mut();
    v_res_6184_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryGT_match__1_splitter(v_00_u03b1_6174_, v_00_u03b2_6175_, v_inst_6176_, v_k_6177_, v_motive_6178_, v_x_6179_, v_x_6180_, v_x_6181_, v_h__1_6182_, v_h__2_6183_);
    lean_dec(v_k_6177_);
    lean_dec_ref(v_inst_6176_);
    return v_res_6184_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___redArg(
    mut v_x_6185_: *mut LeanObject,
    mut v_h__1_6186_: *mut LeanObject,
    mut v_h__2_6187_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6185_) == 0 {
        let mut v_size_6188_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6189_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6190_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6191_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6186_);
        v_size_6188_ = lean_ctor_get(v_x_6185_, 0);
        lean_inc(v_size_6188_);
        v_k_6189_ = lean_ctor_get(v_x_6185_, 1);
        lean_inc(v_k_6189_);
        v_v_6190_ = lean_ctor_get(v_x_6185_, 2);
        lean_inc(v_v_6190_);
        v_l_6191_ = lean_ctor_get(v_x_6185_, 3);
        lean_inc(v_l_6191_);
        v_r_6192_ = lean_ctor_get(v_x_6185_, 4);
        lean_inc(v_r_6192_);
        lean_dec_ref_known(v_x_6185_, 5);
        v___x_6193_ = lean_apply_7(
            v_h__2_6187_,
            v_size_6188_,
            v_k_6189_,
            v_v_6190_,
            v_l_6191_,
            v_r_6192_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6193_;
    } else {
        let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6187_);
        v___x_6194_ = lean_apply_2(v_h__1_6186_, lean_box(0), lean_box(0));
        return v___x_6194_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(
    mut v_00_u03b1_6195_: *mut LeanObject,
    mut v_00_u03b2_6196_: *mut LeanObject,
    mut v_inst_6197_: *mut LeanObject,
    mut v_k_6198_: *mut LeanObject,
    mut v_motive_6199_: *mut LeanObject,
    mut v_x_6200_: *mut LeanObject,
    mut v_x_6201_: *mut LeanObject,
    mut v_x_6202_: *mut LeanObject,
    mut v_h__1_6203_: *mut LeanObject,
    mut v_h__2_6204_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6200_) == 0 {
        let mut v_size_6205_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6206_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6207_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6208_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6203_);
        v_size_6205_ = lean_ctor_get(v_x_6200_, 0);
        lean_inc(v_size_6205_);
        v_k_6206_ = lean_ctor_get(v_x_6200_, 1);
        lean_inc(v_k_6206_);
        v_v_6207_ = lean_ctor_get(v_x_6200_, 2);
        lean_inc(v_v_6207_);
        v_l_6208_ = lean_ctor_get(v_x_6200_, 3);
        lean_inc(v_l_6208_);
        v_r_6209_ = lean_ctor_get(v_x_6200_, 4);
        lean_inc(v_r_6209_);
        lean_dec_ref_known(v_x_6200_, 5);
        v___x_6210_ = lean_apply_7(
            v_h__2_6204_,
            v_size_6205_,
            v_k_6206_,
            v_v_6207_,
            v_l_6208_,
            v_r_6209_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6210_;
    } else {
        let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6204_);
        v___x_6211_ = lean_apply_2(v_h__1_6203_, lean_box(0), lean_box(0));
        return v___x_6211_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter___boxed(
    mut v_00_u03b1_6212_: *mut LeanObject,
    mut v_00_u03b2_6213_: *mut LeanObject,
    mut v_inst_6214_: *mut LeanObject,
    mut v_k_6215_: *mut LeanObject,
    mut v_motive_6216_: *mut LeanObject,
    mut v_x_6217_: *mut LeanObject,
    mut v_x_6218_: *mut LeanObject,
    mut v_x_6219_: *mut LeanObject,
    mut v_h__1_6220_: *mut LeanObject,
    mut v_h__2_6221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6222_: *mut LeanObject = core::ptr::null_mut();
    v_res_6222_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLE_match__1_splitter(v_00_u03b1_6212_, v_00_u03b2_6213_, v_inst_6214_, v_k_6215_, v_motive_6216_, v_x_6217_, v_x_6218_, v_x_6219_, v_h__1_6220_, v_h__2_6221_);
    lean_dec(v_k_6215_);
    lean_dec_ref(v_inst_6214_);
    return v_res_6222_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___redArg(
    mut v_x_6223_: *mut LeanObject,
    mut v_h__1_6224_: *mut LeanObject,
    mut v_h__2_6225_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6223_) == 0 {
        let mut v_size_6226_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6227_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6228_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6229_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6224_);
        v_size_6226_ = lean_ctor_get(v_x_6223_, 0);
        lean_inc(v_size_6226_);
        v_k_6227_ = lean_ctor_get(v_x_6223_, 1);
        lean_inc(v_k_6227_);
        v_v_6228_ = lean_ctor_get(v_x_6223_, 2);
        lean_inc(v_v_6228_);
        v_l_6229_ = lean_ctor_get(v_x_6223_, 3);
        lean_inc(v_l_6229_);
        v_r_6230_ = lean_ctor_get(v_x_6223_, 4);
        lean_inc(v_r_6230_);
        lean_dec_ref_known(v_x_6223_, 5);
        v___x_6231_ = lean_apply_7(
            v_h__2_6225_,
            v_size_6226_,
            v_k_6227_,
            v_v_6228_,
            v_l_6229_,
            v_r_6230_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6231_;
    } else {
        let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6225_);
        v___x_6232_ = lean_apply_2(v_h__1_6224_, lean_box(0), lean_box(0));
        return v___x_6232_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(
    mut v_00_u03b1_6233_: *mut LeanObject,
    mut v_00_u03b2_6234_: *mut LeanObject,
    mut v_inst_6235_: *mut LeanObject,
    mut v_k_6236_: *mut LeanObject,
    mut v_motive_6237_: *mut LeanObject,
    mut v_x_6238_: *mut LeanObject,
    mut v_x_6239_: *mut LeanObject,
    mut v_x_6240_: *mut LeanObject,
    mut v_h__1_6241_: *mut LeanObject,
    mut v_h__2_6242_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6238_) == 0 {
        let mut v_size_6243_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_6244_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_6245_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_6246_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_6247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_6241_);
        v_size_6243_ = lean_ctor_get(v_x_6238_, 0);
        lean_inc(v_size_6243_);
        v_k_6244_ = lean_ctor_get(v_x_6238_, 1);
        lean_inc(v_k_6244_);
        v_v_6245_ = lean_ctor_get(v_x_6238_, 2);
        lean_inc(v_v_6245_);
        v_l_6246_ = lean_ctor_get(v_x_6238_, 3);
        lean_inc(v_l_6246_);
        v_r_6247_ = lean_ctor_get(v_x_6238_, 4);
        lean_inc(v_r_6247_);
        lean_dec_ref_known(v_x_6238_, 5);
        v___x_6248_ = lean_apply_7(
            v_h__2_6242_,
            v_size_6243_,
            v_k_6244_,
            v_v_6245_,
            v_l_6246_,
            v_r_6247_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_6248_;
    } else {
        let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_6242_);
        v___x_6249_ = lean_apply_2(v_h__1_6241_, lean_box(0), lean_box(0));
        return v___x_6249_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter___boxed(
    mut v_00_u03b1_6250_: *mut LeanObject,
    mut v_00_u03b2_6251_: *mut LeanObject,
    mut v_inst_6252_: *mut LeanObject,
    mut v_k_6253_: *mut LeanObject,
    mut v_motive_6254_: *mut LeanObject,
    mut v_x_6255_: *mut LeanObject,
    mut v_x_6256_: *mut LeanObject,
    mut v_x_6257_: *mut LeanObject,
    mut v_h__1_6258_: *mut LeanObject,
    mut v_h__2_6259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6260_: *mut LeanObject = core::ptr::null_mut();
    v_res_6260_ = l___private_Std_Data_DTreeMap_Internal_Model_0__Std_DTreeMap_Internal_Impl_Const_getEntryLT_match__1_splitter(v_00_u03b1_6250_, v_00_u03b2_6251_, v_inst_6252_, v_k_6253_, v_motive_6254_, v_x_6255_, v_x_6256_, v_x_6257_, v_h__1_6258_, v_h__2_6259_);
    lean_dec(v_k_6253_);
    lean_dec_ref(v_inst_6252_);
    return v_res_6260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_Model(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_Model(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_Model(builtin);
}
