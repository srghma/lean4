// Lean compiler output
// Module: Lake.Util.RBArray
// Imports: Std.Data.TreeMap.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___redArg,
};
use crate::r#gen::Std::Data::TreeMap::Basic::{
    initialize_Std_Data_TreeMap_Basic, runtime_initialize_Std_Data_TreeMap_Basic,
};
pub static l_Lake_RBArray_empty___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_RBArray_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_empty___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_RBArray_empty___closed__1_value: leanh::LeanCtorObject<2> =
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
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_RBArray_empty___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_RBArray_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_empty___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_RBArray_all___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_RBArray_all___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_RBArray_all___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_RBArray_empty(
    mut v_00_u03b1_910_: *mut leanh::LeanObject,
    mut v_00_u03b2_911_: *mut leanh::LeanObject,
    mut v_cmp_912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lake_RBArray_empty___closed__1;
    return v___x_913_;
}
pub unsafe fn l_Lake_RBArray_empty___boxed(
    mut v_00_u03b1_914_: *mut leanh::LeanObject,
    mut v_00_u03b2_915_: *mut leanh::LeanObject,
    mut v_cmp_916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_917_ = l_Lake_RBArray_empty(v_00_u03b1_914_, v_00_u03b2_915_, v_cmp_916_);
    leanh::lean_dec_ref(v_cmp_916_);
    return v_res_917_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(
    mut v_cmp_918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_919_ = l_Lake_RBArray_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_cmp_918_,
    );
    return v___x_919_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg___boxed(
    mut v_cmp_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ =
        l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(v_cmp_920_);
    leanh::lean_dec_ref(v_cmp_920_);
    return v_res_921_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(
    mut v_00_u03b1_922_: *mut leanh::LeanObject,
    mut v_00_u03b2_923_: *mut leanh::LeanObject,
    mut v_cmp_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Lake_RBArray_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_cmp_924_,
    );
    return v___x_925_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___boxed(
    mut v_00_u03b1_926_: *mut leanh::LeanObject,
    mut v_00_u03b2_927_: *mut leanh::LeanObject,
    mut v_cmp_928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_929_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(
        v_00_u03b1_926_,
        v_00_u03b2_927_,
        v_cmp_928_,
    );
    leanh::lean_dec_ref(v_cmp_928_);
    return v_res_929_;
}
pub unsafe fn l_Lake_RBArray_mkEmpty___redArg(
    mut v_size_930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = leanh::lean_box(1);
    v___x_932_ = lean_mk_empty_array_with_capacity(v_size_930_);
    v___x_933_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_933_, 0, v___x_931_);
    leanh::lean_ctor_set(v___x_933_, 1, v___x_932_);
    return v___x_933_;
}
pub unsafe fn l_Lake_RBArray_mkEmpty___redArg___boxed(
    mut v_size_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_935_ = l_Lake_RBArray_mkEmpty___redArg(v_size_934_);
    leanh::lean_dec(v_size_934_);
    return v_res_935_;
}
pub unsafe fn l_Lake_RBArray_mkEmpty(
    mut v_00_u03b1_936_: *mut leanh::LeanObject,
    mut v_00_u03b2_937_: *mut leanh::LeanObject,
    mut v_cmp_938_: *mut leanh::LeanObject,
    mut v_size_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = l_Lake_RBArray_mkEmpty___redArg(v_size_939_);
    return v___x_940_;
}
pub unsafe fn l_Lake_RBArray_mkEmpty___boxed(
    mut v_00_u03b1_941_: *mut leanh::LeanObject,
    mut v_00_u03b2_942_: *mut leanh::LeanObject,
    mut v_cmp_943_: *mut leanh::LeanObject,
    mut v_size_944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_945_ = l_Lake_RBArray_mkEmpty(v_00_u03b1_941_, v_00_u03b2_942_, v_cmp_943_, v_size_944_);
    leanh::lean_dec(v_size_944_);
    leanh::lean_dec_ref(v_cmp_943_);
    return v_res_945_;
}
pub unsafe fn l_Lake_RBArray_find_x3f___redArg(
    mut v_cmp_946_: *mut leanh::LeanObject,
    mut v_self_947_: *mut leanh::LeanObject,
    mut v_a_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toTreeMap_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toTreeMap_949_ = leanh::lean_ctor_get(v_self_947_, 0);
    leanh::lean_inc(v_toTreeMap_949_);
    leanh::lean_dec_ref(v_self_947_);
    v___x_950_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_946_, v_toTreeMap_949_, v_a_948_);
    return v___x_950_;
}
pub unsafe fn l_Lake_RBArray_find_x3f(
    mut v_00_u03b1_951_: *mut leanh::LeanObject,
    mut v_00_u03b2_952_: *mut leanh::LeanObject,
    mut v_cmp_953_: *mut leanh::LeanObject,
    mut v_self_954_: *mut leanh::LeanObject,
    mut v_a_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toTreeMap_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toTreeMap_956_ = leanh::lean_ctor_get(v_self_954_, 0);
    leanh::lean_inc(v_toTreeMap_956_);
    leanh::lean_dec_ref(v_self_954_);
    v___x_957_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_953_, v_toTreeMap_956_, v_a_955_);
    return v___x_957_;
}
pub unsafe fn l_Lake_RBArray_contains___redArg(
    mut v_cmp_958_: *mut leanh::LeanObject,
    mut v_self_959_: *mut leanh::LeanObject,
    mut v_a_960_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toTreeMap_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    v_toTreeMap_961_ = leanh::lean_ctor_get(v_self_959_, 0);
    leanh::lean_inc(v_toTreeMap_961_);
    leanh::lean_dec_ref(v_self_959_);
    v___x_962_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_958_, v_a_960_, v_toTreeMap_961_);
    return v___x_962_;
}
pub unsafe fn l_Lake_RBArray_contains___redArg___boxed(
    mut v_cmp_963_: *mut leanh::LeanObject,
    mut v_self_964_: *mut leanh::LeanObject,
    mut v_a_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_966_: u8 = 0;
    let mut v_r_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lake_RBArray_contains___redArg(v_cmp_963_, v_self_964_, v_a_965_);
    v_r_967_ = leanh::lean_box((v_res_966_) as usize);
    return v_r_967_;
}
pub unsafe fn l_Lake_RBArray_contains(
    mut v_00_u03b1_968_: *mut leanh::LeanObject,
    mut v_00_u03b2_969_: *mut leanh::LeanObject,
    mut v_cmp_970_: *mut leanh::LeanObject,
    mut v_self_971_: *mut leanh::LeanObject,
    mut v_a_972_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toTreeMap_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    v_toTreeMap_973_ = leanh::lean_ctor_get(v_self_971_, 0);
    leanh::lean_inc(v_toTreeMap_973_);
    leanh::lean_dec_ref(v_self_971_);
    v___x_974_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_970_, v_a_972_, v_toTreeMap_973_);
    return v___x_974_;
}
pub unsafe fn l_Lake_RBArray_contains___boxed(
    mut v_00_u03b1_975_: *mut leanh::LeanObject,
    mut v_00_u03b2_976_: *mut leanh::LeanObject,
    mut v_cmp_977_: *mut leanh::LeanObject,
    mut v_self_978_: *mut leanh::LeanObject,
    mut v_a_979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_980_: u8 = 0;
    let mut v_r_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_980_ = l_Lake_RBArray_contains(
        v_00_u03b1_975_,
        v_00_u03b2_976_,
        v_cmp_977_,
        v_self_978_,
        v_a_979_,
    );
    v_r_981_ = leanh::lean_box((v_res_980_) as usize);
    return v_r_981_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(
    mut v_cmp_982_: *mut leanh::LeanObject,
    mut v_k_983_: *mut leanh::LeanObject,
    mut v_v_984_: *mut leanh::LeanObject,
    mut v_t_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_993_: u8 = 0;
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: u8 = 0;
    let mut v_impl_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1014_: u8 = 0;
    let mut v_size_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1026_: u8 = 0;
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v_unused_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1070_: u8 = 0;
    let mut v_unused_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut v_unused_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1089_: u8 = 0;
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut v_unused_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v_k_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1121_: u8 = 0;
    let mut v_unused_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_unused_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: u8 = 0;
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v_size_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut v_unused_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1204_: u8 = 0;
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1208_: u8 = 0;
    let mut v_unused_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1215_: u8 = 0;
    let mut v_unused_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v_k_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1243_: u8 = 0;
    let mut v_unused_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut v_unused_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1255_: u8 = 0;
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut v_unused_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_985_) == 0 {
                    v_size_986_ = leanh::lean_ctor_get(v_t_985_, 0);
                    v_k_987_ = leanh::lean_ctor_get(v_t_985_, 1);
                    v_v_988_ = leanh::lean_ctor_get(v_t_985_, 2);
                    v_l_989_ = leanh::lean_ctor_get(v_t_985_, 3);
                    v_r_990_ = leanh::lean_ctor_get(v_t_985_, 4);
                    v_isSharedCheck_1271_ = (!leanh::lean_is_exclusive(v_t_985_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_992_ = v_t_985_;
                        v_isShared_993_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_990_);
                        leanh::lean_inc(v_l_989_);
                        leanh::lean_inc(v_v_988_);
                        leanh::lean_inc(v_k_987_);
                        leanh::lean_inc(v_size_986_);
                        leanh::lean_dec(v_t_985_);
                        v___x_992_ = leanh::lean_box(0);
                        v_isShared_993_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_cmp_982_);
                    v___x_1272_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1273_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_1273_, 0, v___x_1272_);
                    leanh::lean_ctor_set(v___x_1273_, 1, v_k_983_);
                    leanh::lean_ctor_set(v___x_1273_, 2, v_v_984_);
                    leanh::lean_ctor_set(v___x_1273_, 3, v_t_985_);
                    leanh::lean_ctor_set(v___x_1273_, 4, v_t_985_);
                    return v___x_1273_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_cmp_982_);
                leanh::lean_inc(v_k_987_);
                leanh::lean_inc(v_k_983_);
                v___x_994_ = leanh::lean_apply_2(v_cmp_982_, v_k_983_, v_k_987_);
                v___x_995_ = (leanh::lean_unbox(v___x_994_) as u8);
                match v___x_995_ {
                    0 => {
                        leanh::lean_dec(v_size_986_);
                        v_impl_996_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_982_, v_k_983_, v_v_984_, v_l_989_);
                        v___x_997_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_990_) == 0 {
                            v_size_998_ = leanh::lean_ctor_get(v_r_990_, 0);
                            v_size_999_ = leanh::lean_ctor_get(v_impl_996_, 0);
                            leanh::lean_inc(v_size_999_);
                            v_k_1000_ = leanh::lean_ctor_get(v_impl_996_, 1);
                            leanh::lean_inc(v_k_1000_);
                            v_v_1001_ = leanh::lean_ctor_get(v_impl_996_, 2);
                            leanh::lean_inc(v_v_1001_);
                            v_l_1002_ = leanh::lean_ctor_get(v_impl_996_, 3);
                            leanh::lean_inc(v_l_1002_);
                            v_r_1003_ = leanh::lean_ctor_get(v_impl_996_, 4);
                            leanh::lean_inc(v_r_1003_);
                            v___x_1004_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1005_ = lean_nat_mul(v___x_1004_, v_size_998_);
                            v___x_1006_ = lean_nat_dec_lt(v___x_1005_, v_size_999_);
                            leanh::lean_dec(v___x_1005_);
                            if v___x_1006_ == 0 {
                                leanh::lean_dec(v_r_1003_);
                                leanh::lean_dec(v_l_1002_);
                                leanh::lean_dec(v_v_1001_);
                                leanh::lean_dec(v_k_1000_);
                                v___x_1007_ = lean_nat_add(v___x_997_, v_size_999_);
                                leanh::lean_dec(v_size_999_);
                                v___x_1008_ = lean_nat_add(v___x_1007_, v_size_998_);
                                leanh::lean_dec(v___x_1007_);
                                if v_isShared_993_ == 0 {
                                    leanh::lean_ctor_set(v___x_992_, 3, v_impl_996_);
                                    leanh::lean_ctor_set(v___x_992_, 0, v___x_1008_);
                                    v___x_1010_ = v___x_992_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1011_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1011_,
                                        0,
                                        v___x_1008_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1011_,
                                        1,
                                        v_k_987_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1011_,
                                        2,
                                        v_v_988_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1011_,
                                        3,
                                        v_impl_996_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1011_,
                                        4,
                                        v_r_990_,
                                    );
                                    v___x_1010_ = v_reuseFailAlloc_1011_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1077_ =
                                    (!leanh::lean_is_exclusive(v_impl_996_)) as u8;
                                if v_isSharedCheck_1077_ == 0 {
                                    v_unused_1078_ = leanh::lean_ctor_get(v_impl_996_, 4);
                                    leanh::lean_dec(v_unused_1078_);
                                    v_unused_1079_ = leanh::lean_ctor_get(v_impl_996_, 3);
                                    leanh::lean_dec(v_unused_1079_);
                                    v_unused_1080_ = leanh::lean_ctor_get(v_impl_996_, 2);
                                    leanh::lean_dec(v_unused_1080_);
                                    v_unused_1081_ = leanh::lean_ctor_get(v_impl_996_, 1);
                                    leanh::lean_dec(v_unused_1081_);
                                    v_unused_1082_ = leanh::lean_ctor_get(v_impl_996_, 0);
                                    leanh::lean_dec(v_unused_1082_);
                                    v___x_1013_ = v_impl_996_;
                                    v_isShared_1014_ = v_isSharedCheck_1077_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_996_);
                                    v___x_1013_ = leanh::lean_box(0);
                                    v_isShared_1014_ = v_isSharedCheck_1077_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1083_ = leanh::lean_ctor_get(v_impl_996_, 3);
                            leanh::lean_inc(v_l_1083_);
                            if leanh::lean_obj_tag(v_l_1083_) == 0 {
                                v_r_1084_ = leanh::lean_ctor_get(v_impl_996_, 4);
                                v_k_1085_ = leanh::lean_ctor_get(v_impl_996_, 1);
                                v_v_1086_ = leanh::lean_ctor_get(v_impl_996_, 2);
                                v_isSharedCheck_1097_ =
                                    (!leanh::lean_is_exclusive(v_impl_996_)) as u8;
                                if v_isSharedCheck_1097_ == 0 {
                                    v_unused_1098_ = leanh::lean_ctor_get(v_impl_996_, 3);
                                    leanh::lean_dec(v_unused_1098_);
                                    v_unused_1099_ = leanh::lean_ctor_get(v_impl_996_, 0);
                                    leanh::lean_dec(v_unused_1099_);
                                    v___x_1088_ = v_impl_996_;
                                    v_isShared_1089_ = v_isSharedCheck_1097_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_1084_);
                                    leanh::lean_inc(v_v_1086_);
                                    leanh::lean_inc(v_k_1085_);
                                    leanh::lean_dec(v_impl_996_);
                                    v___x_1088_ = leanh::lean_box(0);
                                    v_isShared_1089_ = v_isSharedCheck_1097_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1100_ = leanh::lean_ctor_get(v_impl_996_, 4);
                                leanh::lean_inc(v_r_1100_);
                                if leanh::lean_obj_tag(v_r_1100_) == 0 {
                                    v_k_1101_ = leanh::lean_ctor_get(v_impl_996_, 1);
                                    v_v_1102_ = leanh::lean_ctor_get(v_impl_996_, 2);
                                    v_isSharedCheck_1125_ =
                                        (!leanh::lean_is_exclusive(v_impl_996_)) as u8;
                                    if v_isSharedCheck_1125_ == 0 {
                                        v_unused_1126_ =
                                            leanh::lean_ctor_get(v_impl_996_, 4);
                                        leanh::lean_dec(v_unused_1126_);
                                        v_unused_1127_ =
                                            leanh::lean_ctor_get(v_impl_996_, 3);
                                        leanh::lean_dec(v_unused_1127_);
                                        v_unused_1128_ =
                                            leanh::lean_ctor_get(v_impl_996_, 0);
                                        leanh::lean_dec(v_unused_1128_);
                                        v___x_1104_ = v_impl_996_;
                                        v_isShared_1105_ = v_isSharedCheck_1125_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_1102_);
                                        leanh::lean_inc(v_k_1101_);
                                        leanh::lean_dec(v_impl_996_);
                                        v___x_1104_ = leanh::lean_box(0);
                                        v_isShared_1105_ = v_isSharedCheck_1125_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1129_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_993_ == 0 {
                                        leanh::lean_ctor_set(v___x_992_, 4, v_r_1100_);
                                        leanh::lean_ctor_set(v___x_992_, 3, v_impl_996_);
                                        leanh::lean_ctor_set(v___x_992_, 0, v___x_1129_);
                                        v___x_1131_ = v___x_992_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1132_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1132_,
                                            0,
                                            v___x_1129_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1132_,
                                            1,
                                            v_k_987_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1132_,
                                            2,
                                            v_v_988_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1132_,
                                            3,
                                            v_impl_996_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1132_,
                                            4,
                                            v_r_1100_,
                                        );
                                        v___x_1131_ = v_reuseFailAlloc_1132_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_988_);
                        leanh::lean_dec(v_k_987_);
                        leanh::lean_dec_ref(v_cmp_982_);
                        if v_isShared_993_ == 0 {
                            leanh::lean_ctor_set(v___x_992_, 2, v_v_984_);
                            leanh::lean_ctor_set(v___x_992_, 1, v_k_983_);
                            v___x_1134_ = v___x_992_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1135_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_size_986_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_983_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_984_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_l_989_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_r_990_);
                            v___x_1134_ = v_reuseFailAlloc_1135_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_986_);
                        v_impl_1136_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_982_, v_k_983_, v_v_984_, v_r_990_);
                        v___x_1137_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_989_) == 0 {
                            v_size_1138_ = leanh::lean_ctor_get(v_l_989_, 0);
                            v_size_1139_ = leanh::lean_ctor_get(v_impl_1136_, 0);
                            leanh::lean_inc(v_size_1139_);
                            v_k_1140_ = leanh::lean_ctor_get(v_impl_1136_, 1);
                            leanh::lean_inc(v_k_1140_);
                            v_v_1141_ = leanh::lean_ctor_get(v_impl_1136_, 2);
                            leanh::lean_inc(v_v_1141_);
                            v_l_1142_ = leanh::lean_ctor_get(v_impl_1136_, 3);
                            leanh::lean_inc(v_l_1142_);
                            v_r_1143_ = leanh::lean_ctor_get(v_impl_1136_, 4);
                            leanh::lean_inc(v_r_1143_);
                            v___x_1144_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1145_ = lean_nat_mul(v___x_1144_, v_size_1138_);
                            v___x_1146_ = lean_nat_dec_lt(v___x_1145_, v_size_1139_);
                            leanh::lean_dec(v___x_1145_);
                            if v___x_1146_ == 0 {
                                leanh::lean_dec(v_r_1143_);
                                leanh::lean_dec(v_l_1142_);
                                leanh::lean_dec(v_v_1141_);
                                leanh::lean_dec(v_k_1140_);
                                v___x_1147_ = lean_nat_add(v___x_1137_, v_size_1138_);
                                v___x_1148_ = lean_nat_add(v___x_1147_, v_size_1139_);
                                leanh::lean_dec(v_size_1139_);
                                leanh::lean_dec(v___x_1147_);
                                if v_isShared_993_ == 0 {
                                    leanh::lean_ctor_set(v___x_992_, 4, v_impl_1136_);
                                    leanh::lean_ctor_set(v___x_992_, 0, v___x_1148_);
                                    v___x_1150_ = v___x_992_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1151_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1151_,
                                        0,
                                        v___x_1148_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1151_,
                                        1,
                                        v_k_987_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1151_,
                                        2,
                                        v_v_988_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1151_,
                                        3,
                                        v_l_989_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1151_,
                                        4,
                                        v_impl_1136_,
                                    );
                                    v___x_1150_ = v_reuseFailAlloc_1151_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1215_ =
                                    (!leanh::lean_is_exclusive(v_impl_1136_)) as u8;
                                if v_isSharedCheck_1215_ == 0 {
                                    v_unused_1216_ = leanh::lean_ctor_get(v_impl_1136_, 4);
                                    leanh::lean_dec(v_unused_1216_);
                                    v_unused_1217_ = leanh::lean_ctor_get(v_impl_1136_, 3);
                                    leanh::lean_dec(v_unused_1217_);
                                    v_unused_1218_ = leanh::lean_ctor_get(v_impl_1136_, 2);
                                    leanh::lean_dec(v_unused_1218_);
                                    v_unused_1219_ = leanh::lean_ctor_get(v_impl_1136_, 1);
                                    leanh::lean_dec(v_unused_1219_);
                                    v_unused_1220_ = leanh::lean_ctor_get(v_impl_1136_, 0);
                                    leanh::lean_dec(v_unused_1220_);
                                    v___x_1153_ = v_impl_1136_;
                                    v_isShared_1154_ = v_isSharedCheck_1215_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_1136_);
                                    v___x_1153_ = leanh::lean_box(0);
                                    v_isShared_1154_ = v_isSharedCheck_1215_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1221_ = leanh::lean_ctor_get(v_impl_1136_, 3);
                            leanh::lean_inc(v_l_1221_);
                            if leanh::lean_obj_tag(v_l_1221_) == 0 {
                                v_r_1222_ = leanh::lean_ctor_get(v_impl_1136_, 4);
                                v_k_1223_ = leanh::lean_ctor_get(v_impl_1136_, 1);
                                v_v_1224_ = leanh::lean_ctor_get(v_impl_1136_, 2);
                                v_isSharedCheck_1247_ =
                                    (!leanh::lean_is_exclusive(v_impl_1136_)) as u8;
                                if v_isSharedCheck_1247_ == 0 {
                                    v_unused_1248_ = leanh::lean_ctor_get(v_impl_1136_, 3);
                                    leanh::lean_dec(v_unused_1248_);
                                    v_unused_1249_ = leanh::lean_ctor_get(v_impl_1136_, 0);
                                    leanh::lean_dec(v_unused_1249_);
                                    v___x_1226_ = v_impl_1136_;
                                    v_isShared_1227_ = v_isSharedCheck_1247_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_1222_);
                                    leanh::lean_inc(v_v_1224_);
                                    leanh::lean_inc(v_k_1223_);
                                    leanh::lean_dec(v_impl_1136_);
                                    v___x_1226_ = leanh::lean_box(0);
                                    v_isShared_1227_ = v_isSharedCheck_1247_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1250_ = leanh::lean_ctor_get(v_impl_1136_, 4);
                                leanh::lean_inc(v_r_1250_);
                                if leanh::lean_obj_tag(v_r_1250_) == 0 {
                                    v_k_1251_ = leanh::lean_ctor_get(v_impl_1136_, 1);
                                    v_v_1252_ = leanh::lean_ctor_get(v_impl_1136_, 2);
                                    v_isSharedCheck_1263_ =
                                        (!leanh::lean_is_exclusive(v_impl_1136_)) as u8;
                                    if v_isSharedCheck_1263_ == 0 {
                                        v_unused_1264_ =
                                            leanh::lean_ctor_get(v_impl_1136_, 4);
                                        leanh::lean_dec(v_unused_1264_);
                                        v_unused_1265_ =
                                            leanh::lean_ctor_get(v_impl_1136_, 3);
                                        leanh::lean_dec(v_unused_1265_);
                                        v_unused_1266_ =
                                            leanh::lean_ctor_get(v_impl_1136_, 0);
                                        leanh::lean_dec(v_unused_1266_);
                                        v___x_1254_ = v_impl_1136_;
                                        v_isShared_1255_ = v_isSharedCheck_1263_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_1252_);
                                        leanh::lean_inc(v_k_1251_);
                                        leanh::lean_dec(v_impl_1136_);
                                        v___x_1254_ = leanh::lean_box(0);
                                        v_isShared_1255_ = v_isSharedCheck_1263_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1267_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_993_ == 0 {
                                        leanh::lean_ctor_set(v___x_992_, 4, v_impl_1136_);
                                        leanh::lean_ctor_set(v___x_992_, 3, v_r_1250_);
                                        leanh::lean_ctor_set(v___x_992_, 0, v___x_1267_);
                                        v___x_1269_ = v___x_992_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1270_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1270_,
                                            0,
                                            v___x_1267_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1270_,
                                            1,
                                            v_k_987_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1270_,
                                            2,
                                            v_v_988_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1270_,
                                            3,
                                            v_r_1250_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1270_,
                                            4,
                                            v_impl_1136_,
                                        );
                                        v___x_1269_ = v_reuseFailAlloc_1270_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1010_;
            }
            3 => {
                v_size_1015_ = leanh::lean_ctor_get(v_l_1002_, 0);
                v_size_1016_ = leanh::lean_ctor_get(v_r_1003_, 0);
                v_k_1017_ = leanh::lean_ctor_get(v_r_1003_, 1);
                v_v_1018_ = leanh::lean_ctor_get(v_r_1003_, 2);
                v_l_1019_ = leanh::lean_ctor_get(v_r_1003_, 3);
                v_r_1020_ = leanh::lean_ctor_get(v_r_1003_, 4);
                v___x_1021_ = leanh::lean_unsigned_to_nat(2);
                v___x_1022_ = lean_nat_mul(v___x_1021_, v_size_1015_);
                v___x_1023_ = lean_nat_dec_lt(v_size_1016_, v___x_1022_);
                leanh::lean_dec(v___x_1022_);
                if v___x_1023_ == 0 {
                    leanh::lean_inc(v_r_1020_);
                    leanh::lean_inc(v_l_1019_);
                    leanh::lean_inc(v_v_1018_);
                    leanh::lean_inc(v_k_1017_);
                    v_isSharedCheck_1052_ = (!leanh::lean_is_exclusive(v_r_1003_)) as u8;
                    if v_isSharedCheck_1052_ == 0 {
                        v_unused_1053_ = leanh::lean_ctor_get(v_r_1003_, 4);
                        leanh::lean_dec(v_unused_1053_);
                        v_unused_1054_ = leanh::lean_ctor_get(v_r_1003_, 3);
                        leanh::lean_dec(v_unused_1054_);
                        v_unused_1055_ = leanh::lean_ctor_get(v_r_1003_, 2);
                        leanh::lean_dec(v_unused_1055_);
                        v_unused_1056_ = leanh::lean_ctor_get(v_r_1003_, 1);
                        leanh::lean_dec(v_unused_1056_);
                        v_unused_1057_ = leanh::lean_ctor_get(v_r_1003_, 0);
                        leanh::lean_dec(v_unused_1057_);
                        v___x_1025_ = v_r_1003_;
                        v_isShared_1026_ = v_isSharedCheck_1052_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1003_);
                        v___x_1025_ = leanh::lean_box(0);
                        v_isShared_1026_ = v_isSharedCheck_1052_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_992_);
                    v___x_1058_ = lean_nat_add(v___x_997_, v_size_999_);
                    leanh::lean_dec(v_size_999_);
                    v___x_1059_ = lean_nat_add(v___x_1058_, v_size_998_);
                    leanh::lean_dec(v___x_1058_);
                    v___x_1060_ = lean_nat_add(v___x_997_, v_size_998_);
                    v___x_1061_ = lean_nat_add(v___x_1060_, v_size_1016_);
                    leanh::lean_dec(v___x_1060_);
                    leanh::lean_inc_ref(v_r_990_);
                    if v_isShared_1014_ == 0 {
                        leanh::lean_ctor_set(v___x_1013_, 4, v_r_990_);
                        leanh::lean_ctor_set(v___x_1013_, 3, v_r_1003_);
                        leanh::lean_ctor_set(v___x_1013_, 2, v_v_988_);
                        leanh::lean_ctor_set(v___x_1013_, 1, v_k_987_);
                        leanh::lean_ctor_set(v___x_1013_, 0, v___x_1061_);
                        v___x_1063_ = v___x_1013_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1076_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1061_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_k_987_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_v_988_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_r_1003_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_r_990_);
                        v___x_1063_ = v_reuseFailAlloc_1076_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1027_ = lean_nat_add(v___x_997_, v_size_999_);
                leanh::lean_dec(v_size_999_);
                v___x_1028_ = lean_nat_add(v___x_1027_, v_size_998_);
                leanh::lean_dec(v___x_1027_);
                v___x_1040_ = lean_nat_add(v___x_997_, v_size_1015_);
                if leanh::lean_obj_tag(v_l_1019_) == 0 {
                    v_size_1050_ = leanh::lean_ctor_get(v_l_1019_, 0);
                    leanh::lean_inc(v_size_1050_);
                    v___y_1042_ = v_size_1050_;
                    state = 8;
                    continue;
                } else {
                    v___x_1051_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1042_ = v___x_1051_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1033_ = lean_nat_add(v___y_1031_, v___y_1032_);
                leanh::lean_dec(v___y_1032_);
                leanh::lean_dec(v___y_1031_);
                if v_isShared_1026_ == 0 {
                    leanh::lean_ctor_set(v___x_1025_, 4, v_r_990_);
                    leanh::lean_ctor_set(v___x_1025_, 3, v_r_1020_);
                    leanh::lean_ctor_set(v___x_1025_, 2, v_v_988_);
                    leanh::lean_ctor_set(v___x_1025_, 1, v_k_987_);
                    leanh::lean_ctor_set(v___x_1025_, 0, v___x_1033_);
                    v___x_1035_ = v___x_1025_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_v_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_r_1020_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_r_990_);
                    v___x_1035_ = v_reuseFailAlloc_1039_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1014_ == 0 {
                    leanh::lean_ctor_set(v___x_1013_, 4, v___x_1035_);
                    leanh::lean_ctor_set(v___x_1013_, 3, v___y_1030_);
                    leanh::lean_ctor_set(v___x_1013_, 2, v_v_1018_);
                    leanh::lean_ctor_set(v___x_1013_, 1, v_k_1017_);
                    leanh::lean_ctor_set(v___x_1013_, 0, v___x_1028_);
                    v___x_1037_ = v___x_1013_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_k_1017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_v_1018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 3, v___y_1030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 4, v___x_1035_);
                    v___x_1037_ = v_reuseFailAlloc_1038_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1037_;
            }
            8 => {
                v___x_1043_ = lean_nat_add(v___x_1040_, v___y_1042_);
                leanh::lean_dec(v___y_1042_);
                leanh::lean_dec(v___x_1040_);
                if v_isShared_993_ == 0 {
                    leanh::lean_ctor_set(v___x_992_, 4, v_l_1019_);
                    leanh::lean_ctor_set(v___x_992_, 3, v_l_1002_);
                    leanh::lean_ctor_set(v___x_992_, 2, v_v_1001_);
                    leanh::lean_ctor_set(v___x_992_, 1, v_k_1000_);
                    leanh::lean_ctor_set(v___x_992_, 0, v___x_1043_);
                    v___x_1045_ = v___x_992_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1049_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_1000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_1001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_l_1002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_l_1019_);
                    v___x_1045_ = v_reuseFailAlloc_1049_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1046_ = lean_nat_add(v___x_997_, v_size_998_);
                if leanh::lean_obj_tag(v_r_1020_) == 0 {
                    v_size_1047_ = leanh::lean_ctor_get(v_r_1020_, 0);
                    leanh::lean_inc(v_size_1047_);
                    v___y_1030_ = v___x_1045_;
                    v___y_1031_ = v___x_1046_;
                    v___y_1032_ = v_size_1047_;
                    state = 5;
                    continue;
                } else {
                    v___x_1048_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1030_ = v___x_1045_;
                    v___y_1031_ = v___x_1046_;
                    v___y_1032_ = v___x_1048_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1070_ = (!leanh::lean_is_exclusive(v_r_990_)) as u8;
                if v_isSharedCheck_1070_ == 0 {
                    v_unused_1071_ = leanh::lean_ctor_get(v_r_990_, 4);
                    leanh::lean_dec(v_unused_1071_);
                    v_unused_1072_ = leanh::lean_ctor_get(v_r_990_, 3);
                    leanh::lean_dec(v_unused_1072_);
                    v_unused_1073_ = leanh::lean_ctor_get(v_r_990_, 2);
                    leanh::lean_dec(v_unused_1073_);
                    v_unused_1074_ = leanh::lean_ctor_get(v_r_990_, 1);
                    leanh::lean_dec(v_unused_1074_);
                    v_unused_1075_ = leanh::lean_ctor_get(v_r_990_, 0);
                    leanh::lean_dec(v_unused_1075_);
                    v___x_1065_ = v_r_990_;
                    v_isShared_1066_ = v_isSharedCheck_1070_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_990_);
                    v___x_1065_ = leanh::lean_box(0);
                    v_isShared_1066_ = v_isSharedCheck_1070_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1066_ == 0 {
                    leanh::lean_ctor_set(v___x_1065_, 4, v___x_1063_);
                    leanh::lean_ctor_set(v___x_1065_, 3, v_l_1002_);
                    leanh::lean_ctor_set(v___x_1065_, 2, v_v_1001_);
                    leanh::lean_ctor_set(v___x_1065_, 1, v_k_1000_);
                    leanh::lean_ctor_set(v___x_1065_, 0, v___x_1059_);
                    v___x_1068_ = v___x_1065_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1069_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_k_1000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_v_1001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_l_1002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___x_1063_);
                    v___x_1068_ = v_reuseFailAlloc_1069_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1068_;
            }
            13 => {
                v___x_1090_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_1084_);
                if v_isShared_1089_ == 0 {
                    leanh::lean_ctor_set(v___x_1088_, 3, v_r_1084_);
                    leanh::lean_ctor_set(v___x_1088_, 2, v_v_988_);
                    leanh::lean_ctor_set(v___x_1088_, 1, v_k_987_);
                    leanh::lean_ctor_set(v___x_1088_, 0, v___x_997_);
                    v___x_1092_ = v___x_1088_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_k_987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_v_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_r_1084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_r_1084_);
                    v___x_1092_ = v_reuseFailAlloc_1096_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_993_ == 0 {
                    leanh::lean_ctor_set(v___x_992_, 4, v___x_1092_);
                    leanh::lean_ctor_set(v___x_992_, 3, v_l_1083_);
                    leanh::lean_ctor_set(v___x_992_, 2, v_v_1086_);
                    leanh::lean_ctor_set(v___x_992_, 1, v_k_1085_);
                    leanh::lean_ctor_set(v___x_992_, 0, v___x_1090_);
                    v___x_1094_ = v___x_992_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_1085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_1086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_l_1083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 4, v___x_1092_);
                    v___x_1094_ = v_reuseFailAlloc_1095_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1094_;
            }
            16 => {
                v_k_1106_ = leanh::lean_ctor_get(v_r_1100_, 1);
                v_v_1107_ = leanh::lean_ctor_get(v_r_1100_, 2);
                v_isSharedCheck_1121_ = (!leanh::lean_is_exclusive(v_r_1100_)) as u8;
                if v_isSharedCheck_1121_ == 0 {
                    v_unused_1122_ = leanh::lean_ctor_get(v_r_1100_, 4);
                    leanh::lean_dec(v_unused_1122_);
                    v_unused_1123_ = leanh::lean_ctor_get(v_r_1100_, 3);
                    leanh::lean_dec(v_unused_1123_);
                    v_unused_1124_ = leanh::lean_ctor_get(v_r_1100_, 0);
                    leanh::lean_dec(v_unused_1124_);
                    v___x_1109_ = v_r_1100_;
                    v_isShared_1110_ = v_isSharedCheck_1121_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1107_);
                    leanh::lean_inc(v_k_1106_);
                    leanh::lean_dec(v_r_1100_);
                    v___x_1109_ = leanh::lean_box(0);
                    v_isShared_1110_ = v_isSharedCheck_1121_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1111_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1110_ == 0 {
                    leanh::lean_ctor_set(v___x_1109_, 4, v_l_1083_);
                    leanh::lean_ctor_set(v___x_1109_, 3, v_l_1083_);
                    leanh::lean_ctor_set(v___x_1109_, 2, v_v_1102_);
                    leanh::lean_ctor_set(v___x_1109_, 1, v_k_1101_);
                    leanh::lean_ctor_set(v___x_1109_, 0, v___x_997_);
                    v___x_1113_ = v___x_1109_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1120_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_k_1101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_v_1102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_l_1083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_l_1083_);
                    v___x_1113_ = v_reuseFailAlloc_1120_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1105_ == 0 {
                    leanh::lean_ctor_set(v___x_1104_, 4, v_l_1083_);
                    leanh::lean_ctor_set(v___x_1104_, 2, v_v_988_);
                    leanh::lean_ctor_set(v___x_1104_, 1, v_k_987_);
                    leanh::lean_ctor_set(v___x_1104_, 0, v___x_997_);
                    v___x_1115_ = v___x_1104_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1119_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_k_987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 2, v_v_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 3, v_l_1083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 4, v_l_1083_);
                    v___x_1115_ = v_reuseFailAlloc_1119_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_993_ == 0 {
                    leanh::lean_ctor_set(v___x_992_, 4, v___x_1115_);
                    leanh::lean_ctor_set(v___x_992_, 3, v___x_1113_);
                    leanh::lean_ctor_set(v___x_992_, 2, v_v_1107_);
                    leanh::lean_ctor_set(v___x_992_, 1, v_k_1106_);
                    leanh::lean_ctor_set(v___x_992_, 0, v___x_1111_);
                    v___x_1117_ = v___x_992_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1118_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1111_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_k_1106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_v_1107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 3, v___x_1113_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 4, v___x_1115_);
                    v___x_1117_ = v_reuseFailAlloc_1118_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1117_;
            }
            21 => {
                return v___x_1131_;
            }
            22 => {
                return v___x_1134_;
            }
            23 => {
                return v___x_1150_;
            }
            24 => {
                v_size_1155_ = leanh::lean_ctor_get(v_l_1142_, 0);
                v_k_1156_ = leanh::lean_ctor_get(v_l_1142_, 1);
                v_v_1157_ = leanh::lean_ctor_get(v_l_1142_, 2);
                v_l_1158_ = leanh::lean_ctor_get(v_l_1142_, 3);
                v_r_1159_ = leanh::lean_ctor_get(v_l_1142_, 4);
                v_size_1160_ = leanh::lean_ctor_get(v_r_1143_, 0);
                v___x_1161_ = leanh::lean_unsigned_to_nat(2);
                v___x_1162_ = lean_nat_mul(v___x_1161_, v_size_1160_);
                v___x_1163_ = lean_nat_dec_lt(v_size_1155_, v___x_1162_);
                leanh::lean_dec(v___x_1162_);
                if v___x_1163_ == 0 {
                    leanh::lean_inc(v_r_1159_);
                    leanh::lean_inc(v_l_1158_);
                    leanh::lean_inc(v_v_1157_);
                    leanh::lean_inc(v_k_1156_);
                    v_isSharedCheck_1191_ = (!leanh::lean_is_exclusive(v_l_1142_)) as u8;
                    if v_isSharedCheck_1191_ == 0 {
                        v_unused_1192_ = leanh::lean_ctor_get(v_l_1142_, 4);
                        leanh::lean_dec(v_unused_1192_);
                        v_unused_1193_ = leanh::lean_ctor_get(v_l_1142_, 3);
                        leanh::lean_dec(v_unused_1193_);
                        v_unused_1194_ = leanh::lean_ctor_get(v_l_1142_, 2);
                        leanh::lean_dec(v_unused_1194_);
                        v_unused_1195_ = leanh::lean_ctor_get(v_l_1142_, 1);
                        leanh::lean_dec(v_unused_1195_);
                        v_unused_1196_ = leanh::lean_ctor_get(v_l_1142_, 0);
                        leanh::lean_dec(v_unused_1196_);
                        v___x_1165_ = v_l_1142_;
                        v_isShared_1166_ = v_isSharedCheck_1191_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_1142_);
                        v___x_1165_ = leanh::lean_box(0);
                        v_isShared_1166_ = v_isSharedCheck_1191_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_992_);
                    v___x_1197_ = lean_nat_add(v___x_1137_, v_size_1138_);
                    v___x_1198_ = lean_nat_add(v___x_1197_, v_size_1139_);
                    leanh::lean_dec(v_size_1139_);
                    v___x_1199_ = lean_nat_add(v___x_1197_, v_size_1155_);
                    leanh::lean_dec(v___x_1197_);
                    leanh::lean_inc_ref(v_l_989_);
                    if v_isShared_1154_ == 0 {
                        leanh::lean_ctor_set(v___x_1153_, 4, v_l_1142_);
                        leanh::lean_ctor_set(v___x_1153_, 3, v_l_989_);
                        leanh::lean_ctor_set(v___x_1153_, 2, v_v_988_);
                        leanh::lean_ctor_set(v___x_1153_, 1, v_k_987_);
                        leanh::lean_ctor_set(v___x_1153_, 0, v___x_1199_);
                        v___x_1201_ = v___x_1153_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1214_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1199_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_987_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_988_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_l_989_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_l_1142_);
                        v___x_1201_ = v_reuseFailAlloc_1214_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1167_ = lean_nat_add(v___x_1137_, v_size_1138_);
                v___x_1168_ = lean_nat_add(v___x_1167_, v_size_1139_);
                leanh::lean_dec(v_size_1139_);
                if leanh::lean_obj_tag(v_l_1158_) == 0 {
                    v_size_1189_ = leanh::lean_ctor_get(v_l_1158_, 0);
                    leanh::lean_inc(v_size_1189_);
                    v___y_1181_ = v_size_1189_;
                    state = 29;
                    continue;
                } else {
                    v___x_1190_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1181_ = v___x_1190_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1173_ = lean_nat_add(v___y_1170_, v___y_1172_);
                leanh::lean_dec(v___y_1172_);
                leanh::lean_dec(v___y_1170_);
                if v_isShared_1166_ == 0 {
                    leanh::lean_ctor_set(v___x_1165_, 4, v_r_1143_);
                    leanh::lean_ctor_set(v___x_1165_, 3, v_r_1159_);
                    leanh::lean_ctor_set(v___x_1165_, 2, v_v_1141_);
                    leanh::lean_ctor_set(v___x_1165_, 1, v_k_1140_);
                    leanh::lean_ctor_set(v___x_1165_, 0, v___x_1173_);
                    v___x_1175_ = v___x_1165_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_k_1140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_v_1141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_r_1159_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_r_1143_);
                    v___x_1175_ = v_reuseFailAlloc_1179_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1154_ == 0 {
                    leanh::lean_ctor_set(v___x_1153_, 4, v___x_1175_);
                    leanh::lean_ctor_set(v___x_1153_, 3, v___y_1171_);
                    leanh::lean_ctor_set(v___x_1153_, 2, v_v_1157_);
                    leanh::lean_ctor_set(v___x_1153_, 1, v_k_1156_);
                    leanh::lean_ctor_set(v___x_1153_, 0, v___x_1168_);
                    v___x_1177_ = v___x_1153_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1168_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_k_1156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_v_1157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 3, v___y_1171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 4, v___x_1175_);
                    v___x_1177_ = v_reuseFailAlloc_1178_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1177_;
            }
            29 => {
                v___x_1182_ = lean_nat_add(v___x_1167_, v___y_1181_);
                leanh::lean_dec(v___y_1181_);
                leanh::lean_dec(v___x_1167_);
                if v_isShared_993_ == 0 {
                    leanh::lean_ctor_set(v___x_992_, 4, v_l_1158_);
                    leanh::lean_ctor_set(v___x_992_, 0, v___x_1182_);
                    v___x_1184_ = v___x_992_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1188_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_k_987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_v_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_l_989_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_l_1158_);
                    v___x_1184_ = v_reuseFailAlloc_1188_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1185_ = lean_nat_add(v___x_1137_, v_size_1160_);
                if leanh::lean_obj_tag(v_r_1159_) == 0 {
                    v_size_1186_ = leanh::lean_ctor_get(v_r_1159_, 0);
                    leanh::lean_inc(v_size_1186_);
                    v___y_1170_ = v___x_1185_;
                    v___y_1171_ = v___x_1184_;
                    v___y_1172_ = v_size_1186_;
                    state = 26;
                    continue;
                } else {
                    v___x_1187_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1170_ = v___x_1185_;
                    v___y_1171_ = v___x_1184_;
                    v___y_1172_ = v___x_1187_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1208_ = (!leanh::lean_is_exclusive(v_l_989_)) as u8;
                if v_isSharedCheck_1208_ == 0 {
                    v_unused_1209_ = leanh::lean_ctor_get(v_l_989_, 4);
                    leanh::lean_dec(v_unused_1209_);
                    v_unused_1210_ = leanh::lean_ctor_get(v_l_989_, 3);
                    leanh::lean_dec(v_unused_1210_);
                    v_unused_1211_ = leanh::lean_ctor_get(v_l_989_, 2);
                    leanh::lean_dec(v_unused_1211_);
                    v_unused_1212_ = leanh::lean_ctor_get(v_l_989_, 1);
                    leanh::lean_dec(v_unused_1212_);
                    v_unused_1213_ = leanh::lean_ctor_get(v_l_989_, 0);
                    leanh::lean_dec(v_unused_1213_);
                    v___x_1203_ = v_l_989_;
                    v_isShared_1204_ = v_isSharedCheck_1208_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_989_);
                    v___x_1203_ = leanh::lean_box(0);
                    v_isShared_1204_ = v_isSharedCheck_1208_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1204_ == 0 {
                    leanh::lean_ctor_set(v___x_1203_, 4, v_r_1143_);
                    leanh::lean_ctor_set(v___x_1203_, 3, v___x_1201_);
                    leanh::lean_ctor_set(v___x_1203_, 2, v_v_1141_);
                    leanh::lean_ctor_set(v___x_1203_, 1, v_k_1140_);
                    leanh::lean_ctor_set(v___x_1203_, 0, v___x_1198_);
                    v___x_1206_ = v___x_1203_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_k_1140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_v_1141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 3, v___x_1201_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_r_1143_);
                    v___x_1206_ = v_reuseFailAlloc_1207_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1206_;
            }
            34 => {
                v_k_1228_ = leanh::lean_ctor_get(v_l_1221_, 1);
                v_v_1229_ = leanh::lean_ctor_get(v_l_1221_, 2);
                v_isSharedCheck_1243_ = (!leanh::lean_is_exclusive(v_l_1221_)) as u8;
                if v_isSharedCheck_1243_ == 0 {
                    v_unused_1244_ = leanh::lean_ctor_get(v_l_1221_, 4);
                    leanh::lean_dec(v_unused_1244_);
                    v_unused_1245_ = leanh::lean_ctor_get(v_l_1221_, 3);
                    leanh::lean_dec(v_unused_1245_);
                    v_unused_1246_ = leanh::lean_ctor_get(v_l_1221_, 0);
                    leanh::lean_dec(v_unused_1246_);
                    v___x_1231_ = v_l_1221_;
                    v_isShared_1232_ = v_isSharedCheck_1243_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1229_);
                    leanh::lean_inc(v_k_1228_);
                    leanh::lean_dec(v_l_1221_);
                    v___x_1231_ = leanh::lean_box(0);
                    v_isShared_1232_ = v_isSharedCheck_1243_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1233_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_1222_, 2);
                if v_isShared_1232_ == 0 {
                    leanh::lean_ctor_set(v___x_1231_, 4, v_r_1222_);
                    leanh::lean_ctor_set(v___x_1231_, 3, v_r_1222_);
                    leanh::lean_ctor_set(v___x_1231_, 2, v_v_988_);
                    leanh::lean_ctor_set(v___x_1231_, 1, v_k_987_);
                    leanh::lean_ctor_set(v___x_1231_, 0, v___x_1137_);
                    v___x_1235_ = v___x_1231_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1242_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_k_987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_v_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_r_1222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_r_1222_);
                    v___x_1235_ = v_reuseFailAlloc_1242_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_1222_);
                if v_isShared_1227_ == 0 {
                    leanh::lean_ctor_set(v___x_1226_, 3, v_r_1222_);
                    leanh::lean_ctor_set(v___x_1226_, 0, v___x_1137_);
                    v___x_1237_ = v___x_1226_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1241_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_k_1223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_v_1224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_r_1222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_r_1222_);
                    v___x_1237_ = v_reuseFailAlloc_1241_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_993_ == 0 {
                    leanh::lean_ctor_set(v___x_992_, 4, v___x_1237_);
                    leanh::lean_ctor_set(v___x_992_, 3, v___x_1235_);
                    leanh::lean_ctor_set(v___x_992_, 2, v_v_1229_);
                    leanh::lean_ctor_set(v___x_992_, 1, v_k_1228_);
                    leanh::lean_ctor_set(v___x_992_, 0, v___x_1233_);
                    v___x_1239_ = v___x_992_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 3, v___x_1235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 4, v___x_1237_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1239_;
            }
            39 => {
                v___x_1256_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1255_ == 0 {
                    leanh::lean_ctor_set(v___x_1254_, 4, v_l_1221_);
                    leanh::lean_ctor_set(v___x_1254_, 2, v_v_988_);
                    leanh::lean_ctor_set(v___x_1254_, 1, v_k_987_);
                    leanh::lean_ctor_set(v___x_1254_, 0, v___x_1137_);
                    v___x_1258_ = v___x_1254_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_k_987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_v_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 3, v_l_1221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 4, v_l_1221_);
                    v___x_1258_ = v_reuseFailAlloc_1262_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_993_ == 0 {
                    leanh::lean_ctor_set(v___x_992_, 4, v_r_1250_);
                    leanh::lean_ctor_set(v___x_992_, 3, v___x_1258_);
                    leanh::lean_ctor_set(v___x_992_, 2, v_v_1252_);
                    leanh::lean_ctor_set(v___x_992_, 1, v_k_1251_);
                    leanh::lean_ctor_set(v___x_992_, 0, v___x_1256_);
                    v___x_1260_ = v___x_992_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1252_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 3, v___x_1258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_r_1250_);
                    v___x_1260_ = v_reuseFailAlloc_1261_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1260_;
            }
            42 => {
                return v___x_1269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(
    mut v_cmp_1274_: *mut leanh::LeanObject,
    mut v_k_1275_: *mut leanh::LeanObject,
    mut v_t_1276_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u8 = 0;
    let mut v___x_1283_: u8 = 0;
    let mut v___x_1285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1276_) == 0 {
                    v_k_1277_ = leanh::lean_ctor_get(v_t_1276_, 1);
                    leanh::lean_inc(v_k_1277_);
                    v_l_1278_ = leanh::lean_ctor_get(v_t_1276_, 3);
                    leanh::lean_inc(v_l_1278_);
                    v_r_1279_ = leanh::lean_ctor_get(v_t_1276_, 4);
                    leanh::lean_inc(v_r_1279_);
                    leanh::lean_dec_ref_known(v_t_1276_, 5);
                    leanh::lean_inc_ref(v_cmp_1274_);
                    leanh::lean_inc(v_k_1275_);
                    v___x_1280_ = leanh::lean_apply_2(v_cmp_1274_, v_k_1275_, v_k_1277_);
                    v___x_1281_ = (leanh::lean_unbox(v___x_1280_) as u8);
                    match v___x_1281_ {
                        0 => {
                            leanh::lean_dec(v_r_1279_);
                            v_t_1276_ = v_l_1278_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_dec(v_r_1279_);
                            leanh::lean_dec(v_l_1278_);
                            leanh::lean_dec(v_k_1275_);
                            leanh::lean_dec_ref(v_cmp_1274_);
                            v___x_1283_ = 1;
                            return v___x_1283_;
                        }
                        _ => {
                            leanh::lean_dec(v_l_1278_);
                            v_t_1276_ = v_r_1279_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_k_1275_);
                    leanh::lean_dec_ref(v_cmp_1274_);
                    v___x_1285_ = 0;
                    return v___x_1285_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg___boxed(
    mut v_cmp_1286_: *mut leanh::LeanObject,
    mut v_k_1287_: *mut leanh::LeanObject,
    mut v_t_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1289_: u8 = 0;
    let mut v_r_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(
            v_cmp_1286_,
            v_k_1287_,
            v_t_1288_,
        );
    v_r_1290_ = leanh::lean_box((v_res_1289_) as usize);
    return v_r_1290_;
}
pub unsafe fn l_Lake_RBArray_insert___redArg(
    mut v_cmp_1291_: *mut leanh::LeanObject,
    mut v_self_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
    mut v_b_1294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toTreeMap_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toArray_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_unused_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toTreeMap_1295_ = leanh::lean_ctor_get(v_self_1292_, 0);
                v_toArray_1296_ = leanh::lean_ctor_get(v_self_1292_, 1);
                leanh::lean_inc(v_toTreeMap_1295_);
                leanh::lean_inc(v_a_1293_);
                leanh::lean_inc_ref(v_cmp_1291_);
                v___x_1297_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_1291_, v_a_1293_, v_toTreeMap_1295_);
                if v___x_1297_ == 0 {
                    leanh::lean_inc_ref(v_toArray_1296_);
                    leanh::lean_inc(v_toTreeMap_1295_);
                    v_isSharedCheck_1306_ = (!leanh::lean_is_exclusive(v_self_1292_)) as u8;
                    if v_isSharedCheck_1306_ == 0 {
                        v_unused_1307_ = leanh::lean_ctor_get(v_self_1292_, 1);
                        leanh::lean_dec(v_unused_1307_);
                        v_unused_1308_ = leanh::lean_ctor_get(v_self_1292_, 0);
                        leanh::lean_dec(v_unused_1308_);
                        v___x_1299_ = v_self_1292_;
                        v_isShared_1300_ = v_isSharedCheck_1306_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_self_1292_);
                        v___x_1299_ = leanh::lean_box(0);
                        v_isShared_1300_ = v_isSharedCheck_1306_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_1294_);
                    leanh::lean_dec(v_a_1293_);
                    leanh::lean_dec_ref(v_cmp_1291_);
                    return v_self_1292_;
                }
            }
            1 => {
                leanh::lean_inc(v_b_1294_);
                v___x_1301_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_1291_, v_a_1293_, v_b_1294_, v_toTreeMap_1295_);
                v___x_1302_ = lean_array_push(v_toArray_1296_, v_b_1294_);
                if v_isShared_1300_ == 0 {
                    leanh::lean_ctor_set(v___x_1299_, 1, v___x_1302_);
                    leanh::lean_ctor_set(v___x_1299_, 0, v___x_1301_);
                    v___x_1304_ = v___x_1299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
                    v___x_1304_ = v_reuseFailAlloc_1305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_RBArray_insert(
    mut v_00_u03b1_1309_: *mut leanh::LeanObject,
    mut v_00_u03b2_1310_: *mut leanh::LeanObject,
    mut v_cmp_1311_: *mut leanh::LeanObject,
    mut v_self_1312_: *mut leanh::LeanObject,
    mut v_a_1313_: *mut leanh::LeanObject,
    mut v_b_1314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lake_RBArray_insert___redArg(v_cmp_1311_, v_self_1312_, v_a_1313_, v_b_1314_);
    return v___x_1315_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(
    mut v_00_u03b1_1316_: *mut leanh::LeanObject,
    mut v_cmp_1317_: *mut leanh::LeanObject,
    mut v_00_u03b2_1318_: *mut leanh::LeanObject,
    mut v_k_1319_: *mut leanh::LeanObject,
    mut v_t_1320_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1321_: u8 = 0;
    v___x_1321_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(
            v_cmp_1317_,
            v_k_1319_,
            v_t_1320_,
        );
    return v___x_1321_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___boxed(
    mut v_00_u03b1_1322_: *mut leanh::LeanObject,
    mut v_cmp_1323_: *mut leanh::LeanObject,
    mut v_00_u03b2_1324_: *mut leanh::LeanObject,
    mut v_k_1325_: *mut leanh::LeanObject,
    mut v_t_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1327_: u8 = 0;
    let mut v_r_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1327_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(
        v_00_u03b1_1322_,
        v_cmp_1323_,
        v_00_u03b2_1324_,
        v_k_1325_,
        v_t_1326_,
    );
    v_r_1328_ = leanh::lean_box((v_res_1327_) as usize);
    return v_r_1328_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1(
    mut v_00_u03b1_1329_: *mut leanh::LeanObject,
    mut v_cmp_1330_: *mut leanh::LeanObject,
    mut v_00_u03b2_1331_: *mut leanh::LeanObject,
    mut v_k_1332_: *mut leanh::LeanObject,
    mut v_v_1333_: *mut leanh::LeanObject,
    mut v_t_1334_: *mut leanh::LeanObject,
    mut v_hl_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1336_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(
        v_cmp_1330_,
        v_k_1332_,
        v_v_1333_,
        v_t_1334_,
    );
    return v___x_1336_;
}
pub unsafe fn l_Lake_RBArray_all___redArg___lam__0(
    mut v_f_1337_: *mut leanh::LeanObject,
    mut v___x_1338_: u8,
    mut v_v_1339_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    v___x_1340_ = leanh::lean_apply_1(v_f_1337_, v_v_1339_);
    v___x_1341_ = (leanh::lean_unbox(v___x_1340_) as u8);
    if v___x_1341_ == 0 {
        return v___x_1338_;
    } else {
        let mut v___x_1342_: u8 = 0;
        v___x_1342_ = 0;
        return v___x_1342_;
    }
}
pub unsafe fn l_Lake_RBArray_all___redArg___lam__0___boxed(
    mut v_f_1343_: *mut leanh::LeanObject,
    mut v___x_1344_: *mut leanh::LeanObject,
    mut v_v_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_79__boxed_1346_: u8 = 0;
    let mut v_res_1347_: u8 = 0;
    let mut v_r_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_79__boxed_1346_ = (leanh::lean_unbox(v___x_1344_) as u8);
    v_res_1347_ = l_Lake_RBArray_all___redArg___lam__0(v_f_1343_, v___x_79__boxed_1346_, v_v_1345_);
    v_r_1348_ = leanh::lean_box((v_res_1347_) as usize);
    return v_r_1348_;
}
pub unsafe fn l_Lake_RBArray_all___redArg(
    mut v_f_1368_: *mut leanh::LeanObject,
    mut v_self_1369_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toArray_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    v_toArray_1370_ = leanh::lean_ctor_get(v_self_1369_, 1);
    leanh::lean_inc_ref(v_toArray_1370_);
    leanh::lean_dec_ref(v_self_1369_);
    v___x_1371_ = leanh::lean_unsigned_to_nat(0);
    v___x_1372_ = lean_array_get_size(v_toArray_1370_);
    v___x_1373_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1374_ = lean_nat_dec_lt(v___x_1371_, v___x_1372_);
    if v___x_1374_ == 0 {
        let mut v___x_1375_: u8 = 0;
        leanh::lean_dec_ref(v_toArray_1370_);
        leanh::lean_dec_ref(v_f_1368_);
        v___x_1375_ = 1;
        return v___x_1375_;
    } else {
        if v___x_1374_ == 0 {
            leanh::lean_dec_ref(v_toArray_1370_);
            leanh::lean_dec_ref(v_f_1368_);
            return v___x_1374_;
        } else {
            let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1378_: usize = 0;
            let mut v___x_1379_: usize = 0;
            let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1381_: u8 = 0;
            v___x_1376_ = leanh::lean_box((v___x_1374_) as usize);
            v___f_1377_ = leanh::lean_alloc_closure(
                l_Lake_RBArray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_1377_, 0, v_f_1368_);
            leanh::lean_closure_set(v___f_1377_, 1, v___x_1376_);
            v___x_1378_ = 0usize;
            v___x_1379_ = lean_usize_of_nat(v___x_1372_);
            v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1373_,
                v___f_1377_,
                v_toArray_1370_,
                v___x_1378_,
                v___x_1379_,
            );
            v___x_1381_ = (leanh::lean_unbox(v___x_1380_) as u8);
            leanh::lean_dec(v___x_1380_);
            if v___x_1381_ == 0 {
                return v___x_1374_;
            } else {
                let mut v___x_1382_: u8 = 0;
                v___x_1382_ = 0;
                return v___x_1382_;
            }
        }
    }
}
pub unsafe fn l_Lake_RBArray_all___redArg___boxed(
    mut v_f_1383_: *mut leanh::LeanObject,
    mut v_self_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1385_: u8 = 0;
    let mut v_r_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lake_RBArray_all___redArg(v_f_1383_, v_self_1384_);
    v_r_1386_ = leanh::lean_box((v_res_1385_) as usize);
    return v_r_1386_;
}
pub unsafe fn l_Lake_RBArray_all(
    mut v_00_u03b2_1387_: *mut leanh::LeanObject,
    mut v_00_u03b1_1388_: *mut leanh::LeanObject,
    mut v_cmp_1389_: *mut leanh::LeanObject,
    mut v_f_1390_: *mut leanh::LeanObject,
    mut v_self_1391_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toArray_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    v_toArray_1392_ = leanh::lean_ctor_get(v_self_1391_, 1);
    leanh::lean_inc_ref(v_toArray_1392_);
    leanh::lean_dec_ref(v_self_1391_);
    v___x_1393_ = leanh::lean_unsigned_to_nat(0);
    v___x_1394_ = lean_array_get_size(v_toArray_1392_);
    v___x_1395_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1396_ = lean_nat_dec_lt(v___x_1393_, v___x_1394_);
    if v___x_1396_ == 0 {
        let mut v___x_1397_: u8 = 0;
        leanh::lean_dec_ref(v_toArray_1392_);
        leanh::lean_dec_ref(v_f_1390_);
        v___x_1397_ = 1;
        return v___x_1397_;
    } else {
        if v___x_1396_ == 0 {
            leanh::lean_dec_ref(v_toArray_1392_);
            leanh::lean_dec_ref(v_f_1390_);
            return v___x_1396_;
        } else {
            let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1400_: usize = 0;
            let mut v___x_1401_: usize = 0;
            let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1403_: u8 = 0;
            v___x_1398_ = leanh::lean_box((v___x_1396_) as usize);
            v___f_1399_ = leanh::lean_alloc_closure(
                l_Lake_RBArray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_1399_, 0, v_f_1390_);
            leanh::lean_closure_set(v___f_1399_, 1, v___x_1398_);
            v___x_1400_ = 0usize;
            v___x_1401_ = lean_usize_of_nat(v___x_1394_);
            v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1395_,
                v___f_1399_,
                v_toArray_1392_,
                v___x_1400_,
                v___x_1401_,
            );
            v___x_1403_ = (leanh::lean_unbox(v___x_1402_) as u8);
            leanh::lean_dec(v___x_1402_);
            if v___x_1403_ == 0 {
                return v___x_1396_;
            } else {
                let mut v___x_1404_: u8 = 0;
                v___x_1404_ = 0;
                return v___x_1404_;
            }
        }
    }
}
pub unsafe fn l_Lake_RBArray_all___boxed(
    mut v_00_u03b2_1405_: *mut leanh::LeanObject,
    mut v_00_u03b1_1406_: *mut leanh::LeanObject,
    mut v_cmp_1407_: *mut leanh::LeanObject,
    mut v_f_1408_: *mut leanh::LeanObject,
    mut v_self_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1410_: u8 = 0;
    let mut v_r_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1410_ = l_Lake_RBArray_all(
        v_00_u03b2_1405_,
        v_00_u03b1_1406_,
        v_cmp_1407_,
        v_f_1408_,
        v_self_1409_,
    );
    leanh::lean_dec_ref(v_cmp_1407_);
    v_r_1411_ = leanh::lean_box((v_res_1410_) as usize);
    return v_r_1411_;
}
pub unsafe fn l_Lake_RBArray_any___redArg___lam__0(
    mut v_f_1412_: *mut leanh::LeanObject,
    mut v_x_1413_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    v___x_1414_ = leanh::lean_apply_1(v_f_1412_, v_x_1413_);
    v___x_1415_ = (leanh::lean_unbox(v___x_1414_) as u8);
    return v___x_1415_;
}
pub unsafe fn l_Lake_RBArray_any___redArg___lam__0___boxed(
    mut v_f_1416_: *mut leanh::LeanObject,
    mut v_x_1417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1418_: u8 = 0;
    let mut v_r_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ = l_Lake_RBArray_any___redArg___lam__0(v_f_1416_, v_x_1417_);
    v_r_1419_ = leanh::lean_box((v_res_1418_) as usize);
    return v_r_1419_;
}
pub unsafe fn l_Lake_RBArray_any___redArg(
    mut v_f_1420_: *mut leanh::LeanObject,
    mut v_self_1421_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toArray_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    v_toArray_1422_ = leanh::lean_ctor_get(v_self_1421_, 1);
    leanh::lean_inc_ref(v_toArray_1422_);
    leanh::lean_dec_ref(v_self_1421_);
    v___x_1423_ = leanh::lean_unsigned_to_nat(0);
    v___x_1424_ = lean_array_get_size(v_toArray_1422_);
    v___x_1425_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1426_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
    if v___x_1426_ == 0 {
        leanh::lean_dec_ref(v_toArray_1422_);
        leanh::lean_dec_ref(v_f_1420_);
        return v___x_1426_;
    } else {
        if v___x_1426_ == 0 {
            leanh::lean_dec_ref(v_toArray_1422_);
            leanh::lean_dec_ref(v_f_1420_);
            return v___x_1426_;
        } else {
            let mut v___f_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1428_: usize = 0;
            let mut v___x_1429_: usize = 0;
            let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1431_: u8 = 0;
            v___f_1427_ = leanh::lean_alloc_closure(
                l_Lake_RBArray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_1427_, 0, v_f_1420_);
            v___x_1428_ = 0usize;
            v___x_1429_ = lean_usize_of_nat(v___x_1424_);
            v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1425_,
                v___f_1427_,
                v_toArray_1422_,
                v___x_1428_,
                v___x_1429_,
            );
            v___x_1431_ = (leanh::lean_unbox(v___x_1430_) as u8);
            leanh::lean_dec(v___x_1430_);
            return v___x_1431_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_any___redArg___boxed(
    mut v_f_1432_: *mut leanh::LeanObject,
    mut v_self_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1434_: u8 = 0;
    let mut v_r_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lake_RBArray_any___redArg(v_f_1432_, v_self_1433_);
    v_r_1435_ = leanh::lean_box((v_res_1434_) as usize);
    return v_r_1435_;
}
pub unsafe fn l_Lake_RBArray_any(
    mut v_00_u03b2_1436_: *mut leanh::LeanObject,
    mut v_00_u03b1_1437_: *mut leanh::LeanObject,
    mut v_cmp_1438_: *mut leanh::LeanObject,
    mut v_f_1439_: *mut leanh::LeanObject,
    mut v_self_1440_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toArray_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    v_toArray_1441_ = leanh::lean_ctor_get(v_self_1440_, 1);
    leanh::lean_inc_ref(v_toArray_1441_);
    leanh::lean_dec_ref(v_self_1440_);
    v___x_1442_ = leanh::lean_unsigned_to_nat(0);
    v___x_1443_ = lean_array_get_size(v_toArray_1441_);
    v___x_1444_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1445_ = lean_nat_dec_lt(v___x_1442_, v___x_1443_);
    if v___x_1445_ == 0 {
        leanh::lean_dec_ref(v_toArray_1441_);
        leanh::lean_dec_ref(v_f_1439_);
        return v___x_1445_;
    } else {
        if v___x_1445_ == 0 {
            leanh::lean_dec_ref(v_toArray_1441_);
            leanh::lean_dec_ref(v_f_1439_);
            return v___x_1445_;
        } else {
            let mut v___f_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1447_: usize = 0;
            let mut v___x_1448_: usize = 0;
            let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1450_: u8 = 0;
            v___f_1446_ = leanh::lean_alloc_closure(
                l_Lake_RBArray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_1446_, 0, v_f_1439_);
            v___x_1447_ = 0usize;
            v___x_1448_ = lean_usize_of_nat(v___x_1443_);
            v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1444_,
                v___f_1446_,
                v_toArray_1441_,
                v___x_1447_,
                v___x_1448_,
            );
            v___x_1450_ = (leanh::lean_unbox(v___x_1449_) as u8);
            leanh::lean_dec(v___x_1449_);
            return v___x_1450_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_any___boxed(
    mut v_00_u03b2_1451_: *mut leanh::LeanObject,
    mut v_00_u03b1_1452_: *mut leanh::LeanObject,
    mut v_cmp_1453_: *mut leanh::LeanObject,
    mut v_f_1454_: *mut leanh::LeanObject,
    mut v_self_1455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1456_: u8 = 0;
    let mut v_r_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1456_ = l_Lake_RBArray_any(
        v_00_u03b2_1451_,
        v_00_u03b1_1452_,
        v_cmp_1453_,
        v_f_1454_,
        v_self_1455_,
    );
    leanh::lean_dec_ref(v_cmp_1453_);
    v_r_1457_ = leanh::lean_box((v_res_1456_) as usize);
    return v_r_1457_;
}
pub unsafe fn l_Lake_RBArray_foldl___redArg___lam__0(
    mut v_f_1458_: *mut leanh::LeanObject,
    mut v_x1_1459_: *mut leanh::LeanObject,
    mut v_x2_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1461_ = leanh::lean_apply_2(v_f_1458_, v_x1_1459_, v_x2_1460_);
    return v___x_1461_;
}
pub unsafe fn l_Lake_RBArray_foldl___redArg(
    mut v_f_1462_: *mut leanh::LeanObject,
    mut v_init_1463_: *mut leanh::LeanObject,
    mut v_self_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    v_toArray_1465_ = leanh::lean_ctor_get(v_self_1464_, 1);
    leanh::lean_inc_ref(v_toArray_1465_);
    leanh::lean_dec_ref(v_self_1464_);
    v___x_1466_ = leanh::lean_unsigned_to_nat(0);
    v___x_1467_ = lean_array_get_size(v_toArray_1465_);
    v___x_1468_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1469_ = lean_nat_dec_lt(v___x_1466_, v___x_1467_);
    if v___x_1469_ == 0 {
        leanh::lean_dec_ref(v_toArray_1465_);
        leanh::lean_dec(v_f_1462_);
        return v_init_1463_;
    } else {
        let mut v___f_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1471_: u8 = 0;
        v___f_1470_ = leanh::lean_alloc_closure(
            l_Lake_RBArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1470_, 0, v_f_1462_);
        v___x_1471_ = lean_nat_dec_le(v___x_1467_, v___x_1467_);
        if v___x_1471_ == 0 {
            if v___x_1469_ == 0 {
                leanh::lean_dec_ref(v___f_1470_);
                leanh::lean_dec_ref(v_toArray_1465_);
                return v_init_1463_;
            } else {
                let mut v___x_1472_: usize = 0;
                let mut v___x_1473_: usize = 0;
                let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1472_ = 0usize;
                v___x_1473_ = lean_usize_of_nat(v___x_1467_);
                v___x_1474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1468_,
                    v___f_1470_,
                    v_toArray_1465_,
                    v___x_1472_,
                    v___x_1473_,
                    v_init_1463_,
                );
                return v___x_1474_;
            }
        } else {
            let mut v___x_1475_: usize = 0;
            let mut v___x_1476_: usize = 0;
            let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1475_ = 0usize;
            v___x_1476_ = lean_usize_of_nat(v___x_1467_);
            v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1468_,
                v___f_1470_,
                v_toArray_1465_,
                v___x_1475_,
                v___x_1476_,
                v_init_1463_,
            );
            return v___x_1477_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_foldl(
    mut v_00_u03c3_1478_: *mut leanh::LeanObject,
    mut v_00_u03b2_1479_: *mut leanh::LeanObject,
    mut v_00_u03b1_1480_: *mut leanh::LeanObject,
    mut v_cmp_1481_: *mut leanh::LeanObject,
    mut v_f_1482_: *mut leanh::LeanObject,
    mut v_init_1483_: *mut leanh::LeanObject,
    mut v_self_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: u8 = 0;
    v_toArray_1485_ = leanh::lean_ctor_get(v_self_1484_, 1);
    leanh::lean_inc_ref(v_toArray_1485_);
    leanh::lean_dec_ref(v_self_1484_);
    v___x_1486_ = leanh::lean_unsigned_to_nat(0);
    v___x_1487_ = lean_array_get_size(v_toArray_1485_);
    v___x_1488_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1489_ = lean_nat_dec_lt(v___x_1486_, v___x_1487_);
    if v___x_1489_ == 0 {
        leanh::lean_dec_ref(v_toArray_1485_);
        leanh::lean_dec(v_f_1482_);
        return v_init_1483_;
    } else {
        let mut v___f_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1491_: u8 = 0;
        v___f_1490_ = leanh::lean_alloc_closure(
            l_Lake_RBArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1490_, 0, v_f_1482_);
        v___x_1491_ = lean_nat_dec_le(v___x_1487_, v___x_1487_);
        if v___x_1491_ == 0 {
            if v___x_1489_ == 0 {
                leanh::lean_dec_ref(v___f_1490_);
                leanh::lean_dec_ref(v_toArray_1485_);
                return v_init_1483_;
            } else {
                let mut v___x_1492_: usize = 0;
                let mut v___x_1493_: usize = 0;
                let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1492_ = 0usize;
                v___x_1493_ = lean_usize_of_nat(v___x_1487_);
                v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1488_,
                    v___f_1490_,
                    v_toArray_1485_,
                    v___x_1492_,
                    v___x_1493_,
                    v_init_1483_,
                );
                return v___x_1494_;
            }
        } else {
            let mut v___x_1495_: usize = 0;
            let mut v___x_1496_: usize = 0;
            let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1495_ = 0usize;
            v___x_1496_ = lean_usize_of_nat(v___x_1487_);
            v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1488_,
                v___f_1490_,
                v_toArray_1485_,
                v___x_1495_,
                v___x_1496_,
                v_init_1483_,
            );
            return v___x_1497_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_foldl___boxed(
    mut v_00_u03c3_1498_: *mut leanh::LeanObject,
    mut v_00_u03b2_1499_: *mut leanh::LeanObject,
    mut v_00_u03b1_1500_: *mut leanh::LeanObject,
    mut v_cmp_1501_: *mut leanh::LeanObject,
    mut v_f_1502_: *mut leanh::LeanObject,
    mut v_init_1503_: *mut leanh::LeanObject,
    mut v_self_1504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1505_ = l_Lake_RBArray_foldl(
        v_00_u03c3_1498_,
        v_00_u03b2_1499_,
        v_00_u03b1_1500_,
        v_cmp_1501_,
        v_f_1502_,
        v_init_1503_,
        v_self_1504_,
    );
    leanh::lean_dec_ref(v_cmp_1501_);
    return v_res_1505_;
}
pub unsafe fn l_Lake_RBArray_foldlM___redArg(
    mut v_inst_1506_: *mut leanh::LeanObject,
    mut v_f_1507_: *mut leanh::LeanObject,
    mut v_init_1508_: *mut leanh::LeanObject,
    mut v_self_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    v_toArray_1510_ = leanh::lean_ctor_get(v_self_1509_, 1);
    leanh::lean_inc_ref(v_toArray_1510_);
    leanh::lean_dec_ref(v_self_1509_);
    v___x_1511_ = leanh::lean_unsigned_to_nat(0);
    v___x_1512_ = lean_array_get_size(v_toArray_1510_);
    v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
    if v___x_1513_ == 0 {
        let mut v_toApplicative_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1510_);
        leanh::lean_dec(v_f_1507_);
        v_toApplicative_1514_ = leanh::lean_ctor_get(v_inst_1506_, 0);
        leanh::lean_inc_ref(v_toApplicative_1514_);
        leanh::lean_dec_ref(v_inst_1506_);
        v_toPure_1515_ = leanh::lean_ctor_get(v_toApplicative_1514_, 1);
        leanh::lean_inc(v_toPure_1515_);
        leanh::lean_dec_ref(v_toApplicative_1514_);
        v___x_1516_ =
            leanh::lean_apply_2(v_toPure_1515_, leanh::lean_box(0), v_init_1508_);
        return v___x_1516_;
    } else {
        let mut v___x_1517_: u8 = 0;
        v___x_1517_ = lean_nat_dec_le(v___x_1512_, v___x_1512_);
        if v___x_1517_ == 0 {
            if v___x_1513_ == 0 {
                let mut v_toApplicative_1518_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_toArray_1510_);
                leanh::lean_dec(v_f_1507_);
                v_toApplicative_1518_ = leanh::lean_ctor_get(v_inst_1506_, 0);
                leanh::lean_inc_ref(v_toApplicative_1518_);
                leanh::lean_dec_ref(v_inst_1506_);
                v_toPure_1519_ = leanh::lean_ctor_get(v_toApplicative_1518_, 1);
                leanh::lean_inc(v_toPure_1519_);
                leanh::lean_dec_ref(v_toApplicative_1518_);
                v___x_1520_ = leanh::lean_apply_2(
                    v_toPure_1519_,
                    leanh::lean_box(0),
                    v_init_1508_,
                );
                return v___x_1520_;
            } else {
                let mut v___x_1521_: usize = 0;
                let mut v___x_1522_: usize = 0;
                let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1521_ = 0usize;
                v___x_1522_ = lean_usize_of_nat(v___x_1512_);
                v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1506_,
                    v_f_1507_,
                    v_toArray_1510_,
                    v___x_1521_,
                    v___x_1522_,
                    v_init_1508_,
                );
                return v___x_1523_;
            }
        } else {
            let mut v___x_1524_: usize = 0;
            let mut v___x_1525_: usize = 0;
            let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1524_ = 0usize;
            v___x_1525_ = lean_usize_of_nat(v___x_1512_);
            v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1506_,
                v_f_1507_,
                v_toArray_1510_,
                v___x_1524_,
                v___x_1525_,
                v_init_1508_,
            );
            return v___x_1526_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_foldlM(
    mut v_m_1527_: *mut leanh::LeanObject,
    mut v_00_u03c3_1528_: *mut leanh::LeanObject,
    mut v_00_u03b2_1529_: *mut leanh::LeanObject,
    mut v_00_u03b1_1530_: *mut leanh::LeanObject,
    mut v_cmp_1531_: *mut leanh::LeanObject,
    mut v_inst_1532_: *mut leanh::LeanObject,
    mut v_f_1533_: *mut leanh::LeanObject,
    mut v_init_1534_: *mut leanh::LeanObject,
    mut v_self_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    v_toArray_1536_ = leanh::lean_ctor_get(v_self_1535_, 1);
    leanh::lean_inc_ref(v_toArray_1536_);
    leanh::lean_dec_ref(v_self_1535_);
    v___x_1537_ = leanh::lean_unsigned_to_nat(0);
    v___x_1538_ = lean_array_get_size(v_toArray_1536_);
    v___x_1539_ = lean_nat_dec_lt(v___x_1537_, v___x_1538_);
    if v___x_1539_ == 0 {
        let mut v_toApplicative_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1536_);
        leanh::lean_dec(v_f_1533_);
        v_toApplicative_1540_ = leanh::lean_ctor_get(v_inst_1532_, 0);
        leanh::lean_inc_ref(v_toApplicative_1540_);
        leanh::lean_dec_ref(v_inst_1532_);
        v_toPure_1541_ = leanh::lean_ctor_get(v_toApplicative_1540_, 1);
        leanh::lean_inc(v_toPure_1541_);
        leanh::lean_dec_ref(v_toApplicative_1540_);
        v___x_1542_ =
            leanh::lean_apply_2(v_toPure_1541_, leanh::lean_box(0), v_init_1534_);
        return v___x_1542_;
    } else {
        let mut v___x_1543_: u8 = 0;
        v___x_1543_ = lean_nat_dec_le(v___x_1538_, v___x_1538_);
        if v___x_1543_ == 0 {
            if v___x_1539_ == 0 {
                let mut v_toApplicative_1544_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_toArray_1536_);
                leanh::lean_dec(v_f_1533_);
                v_toApplicative_1544_ = leanh::lean_ctor_get(v_inst_1532_, 0);
                leanh::lean_inc_ref(v_toApplicative_1544_);
                leanh::lean_dec_ref(v_inst_1532_);
                v_toPure_1545_ = leanh::lean_ctor_get(v_toApplicative_1544_, 1);
                leanh::lean_inc(v_toPure_1545_);
                leanh::lean_dec_ref(v_toApplicative_1544_);
                v___x_1546_ = leanh::lean_apply_2(
                    v_toPure_1545_,
                    leanh::lean_box(0),
                    v_init_1534_,
                );
                return v___x_1546_;
            } else {
                let mut v___x_1547_: usize = 0;
                let mut v___x_1548_: usize = 0;
                let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1547_ = 0usize;
                v___x_1548_ = lean_usize_of_nat(v___x_1538_);
                v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1532_,
                    v_f_1533_,
                    v_toArray_1536_,
                    v___x_1547_,
                    v___x_1548_,
                    v_init_1534_,
                );
                return v___x_1549_;
            }
        } else {
            let mut v___x_1550_: usize = 0;
            let mut v___x_1551_: usize = 0;
            let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1550_ = 0usize;
            v___x_1551_ = lean_usize_of_nat(v___x_1538_);
            v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1532_,
                v_f_1533_,
                v_toArray_1536_,
                v___x_1550_,
                v___x_1551_,
                v_init_1534_,
            );
            return v___x_1552_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_foldlM___boxed(
    mut v_m_1553_: *mut leanh::LeanObject,
    mut v_00_u03c3_1554_: *mut leanh::LeanObject,
    mut v_00_u03b2_1555_: *mut leanh::LeanObject,
    mut v_00_u03b1_1556_: *mut leanh::LeanObject,
    mut v_cmp_1557_: *mut leanh::LeanObject,
    mut v_inst_1558_: *mut leanh::LeanObject,
    mut v_f_1559_: *mut leanh::LeanObject,
    mut v_init_1560_: *mut leanh::LeanObject,
    mut v_self_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1562_ = l_Lake_RBArray_foldlM(
        v_m_1553_,
        v_00_u03c3_1554_,
        v_00_u03b2_1555_,
        v_00_u03b1_1556_,
        v_cmp_1557_,
        v_inst_1558_,
        v_f_1559_,
        v_init_1560_,
        v_self_1561_,
    );
    leanh::lean_dec_ref(v_cmp_1557_);
    return v_res_1562_;
}
pub unsafe fn l_Lake_RBArray_foldr___redArg(
    mut v_f_1563_: *mut leanh::LeanObject,
    mut v_init_1564_: *mut leanh::LeanObject,
    mut v_self_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    v_toArray_1566_ = leanh::lean_ctor_get(v_self_1565_, 1);
    leanh::lean_inc_ref(v_toArray_1566_);
    leanh::lean_dec_ref(v_self_1565_);
    v___x_1567_ = lean_array_get_size(v_toArray_1566_);
    v___x_1568_ = leanh::lean_unsigned_to_nat(0);
    v___x_1569_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1570_ = lean_nat_dec_lt(v___x_1568_, v___x_1567_);
    if v___x_1570_ == 0 {
        leanh::lean_dec_ref(v_toArray_1566_);
        leanh::lean_dec(v_f_1563_);
        return v_init_1564_;
    } else {
        let mut v___f_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: usize = 0;
        let mut v___x_1573_: usize = 0;
        let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_1571_ = leanh::lean_alloc_closure(
            l_Lake_RBArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1571_, 0, v_f_1563_);
        v___x_1572_ = lean_usize_of_nat(v___x_1567_);
        v___x_1573_ = 0usize;
        v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1569_,
            v___f_1571_,
            v_toArray_1566_,
            v___x_1572_,
            v___x_1573_,
            v_init_1564_,
        );
        return v___x_1574_;
    }
}
pub unsafe fn l_Lake_RBArray_foldr(
    mut v_00_u03b2_1575_: *mut leanh::LeanObject,
    mut v_00_u03c3_1576_: *mut leanh::LeanObject,
    mut v_00_u03b1_1577_: *mut leanh::LeanObject,
    mut v_cmp_1578_: *mut leanh::LeanObject,
    mut v_f_1579_: *mut leanh::LeanObject,
    mut v_init_1580_: *mut leanh::LeanObject,
    mut v_self_1581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: u8 = 0;
    v_toArray_1582_ = leanh::lean_ctor_get(v_self_1581_, 1);
    leanh::lean_inc_ref(v_toArray_1582_);
    leanh::lean_dec_ref(v_self_1581_);
    v___x_1583_ = lean_array_get_size(v_toArray_1582_);
    v___x_1584_ = leanh::lean_unsigned_to_nat(0);
    v___x_1585_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1586_ = lean_nat_dec_lt(v___x_1584_, v___x_1583_);
    if v___x_1586_ == 0 {
        leanh::lean_dec_ref(v_toArray_1582_);
        leanh::lean_dec(v_f_1579_);
        return v_init_1580_;
    } else {
        let mut v___f_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: usize = 0;
        let mut v___x_1589_: usize = 0;
        let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_1587_ = leanh::lean_alloc_closure(
            l_Lake_RBArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1587_, 0, v_f_1579_);
        v___x_1588_ = lean_usize_of_nat(v___x_1583_);
        v___x_1589_ = 0usize;
        v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1585_,
            v___f_1587_,
            v_toArray_1582_,
            v___x_1588_,
            v___x_1589_,
            v_init_1580_,
        );
        return v___x_1590_;
    }
}
pub unsafe fn l_Lake_RBArray_foldr___boxed(
    mut v_00_u03b2_1591_: *mut leanh::LeanObject,
    mut v_00_u03c3_1592_: *mut leanh::LeanObject,
    mut v_00_u03b1_1593_: *mut leanh::LeanObject,
    mut v_cmp_1594_: *mut leanh::LeanObject,
    mut v_f_1595_: *mut leanh::LeanObject,
    mut v_init_1596_: *mut leanh::LeanObject,
    mut v_self_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lake_RBArray_foldr(
        v_00_u03b2_1591_,
        v_00_u03c3_1592_,
        v_00_u03b1_1593_,
        v_cmp_1594_,
        v_f_1595_,
        v_init_1596_,
        v_self_1597_,
    );
    leanh::lean_dec_ref(v_cmp_1594_);
    return v_res_1598_;
}
pub unsafe fn l_Lake_RBArray_foldrM___redArg(
    mut v_inst_1599_: *mut leanh::LeanObject,
    mut v_f_1600_: *mut leanh::LeanObject,
    mut v_init_1601_: *mut leanh::LeanObject,
    mut v_self_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    v_toArray_1603_ = leanh::lean_ctor_get(v_self_1602_, 1);
    leanh::lean_inc_ref(v_toArray_1603_);
    leanh::lean_dec_ref(v_self_1602_);
    v___x_1604_ = lean_array_get_size(v_toArray_1603_);
    v___x_1605_ = leanh::lean_unsigned_to_nat(0);
    v___x_1606_ = lean_nat_dec_lt(v___x_1605_, v___x_1604_);
    if v___x_1606_ == 0 {
        let mut v_toApplicative_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1603_);
        leanh::lean_dec(v_f_1600_);
        v_toApplicative_1607_ = leanh::lean_ctor_get(v_inst_1599_, 0);
        leanh::lean_inc_ref(v_toApplicative_1607_);
        leanh::lean_dec_ref(v_inst_1599_);
        v_toPure_1608_ = leanh::lean_ctor_get(v_toApplicative_1607_, 1);
        leanh::lean_inc(v_toPure_1608_);
        leanh::lean_dec_ref(v_toApplicative_1607_);
        v___x_1609_ =
            leanh::lean_apply_2(v_toPure_1608_, leanh::lean_box(0), v_init_1601_);
        return v___x_1609_;
    } else {
        let mut v___x_1610_: usize = 0;
        let mut v___x_1611_: usize = 0;
        let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1610_ = lean_usize_of_nat(v___x_1604_);
        v___x_1611_ = 0usize;
        v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_1599_,
            v_f_1600_,
            v_toArray_1603_,
            v___x_1610_,
            v___x_1611_,
            v_init_1601_,
        );
        return v___x_1612_;
    }
}
pub unsafe fn l_Lake_RBArray_foldrM(
    mut v_m_1613_: *mut leanh::LeanObject,
    mut v_00_u03b2_1614_: *mut leanh::LeanObject,
    mut v_00_u03c3_1615_: *mut leanh::LeanObject,
    mut v_00_u03b1_1616_: *mut leanh::LeanObject,
    mut v_cmp_1617_: *mut leanh::LeanObject,
    mut v_inst_1618_: *mut leanh::LeanObject,
    mut v_f_1619_: *mut leanh::LeanObject,
    mut v_init_1620_: *mut leanh::LeanObject,
    mut v_self_1621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: u8 = 0;
    v_toArray_1622_ = leanh::lean_ctor_get(v_self_1621_, 1);
    leanh::lean_inc_ref(v_toArray_1622_);
    leanh::lean_dec_ref(v_self_1621_);
    v___x_1623_ = lean_array_get_size(v_toArray_1622_);
    v___x_1624_ = leanh::lean_unsigned_to_nat(0);
    v___x_1625_ = lean_nat_dec_lt(v___x_1624_, v___x_1623_);
    if v___x_1625_ == 0 {
        let mut v_toApplicative_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1622_);
        leanh::lean_dec(v_f_1619_);
        v_toApplicative_1626_ = leanh::lean_ctor_get(v_inst_1618_, 0);
        leanh::lean_inc_ref(v_toApplicative_1626_);
        leanh::lean_dec_ref(v_inst_1618_);
        v_toPure_1627_ = leanh::lean_ctor_get(v_toApplicative_1626_, 1);
        leanh::lean_inc(v_toPure_1627_);
        leanh::lean_dec_ref(v_toApplicative_1626_);
        v___x_1628_ =
            leanh::lean_apply_2(v_toPure_1627_, leanh::lean_box(0), v_init_1620_);
        return v___x_1628_;
    } else {
        let mut v___x_1629_: usize = 0;
        let mut v___x_1630_: usize = 0;
        let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1629_ = lean_usize_of_nat(v___x_1623_);
        v___x_1630_ = 0usize;
        v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_1618_,
            v_f_1619_,
            v_toArray_1622_,
            v___x_1629_,
            v___x_1630_,
            v_init_1620_,
        );
        return v___x_1631_;
    }
}
pub unsafe fn l_Lake_RBArray_foldrM___boxed(
    mut v_m_1632_: *mut leanh::LeanObject,
    mut v_00_u03b2_1633_: *mut leanh::LeanObject,
    mut v_00_u03c3_1634_: *mut leanh::LeanObject,
    mut v_00_u03b1_1635_: *mut leanh::LeanObject,
    mut v_cmp_1636_: *mut leanh::LeanObject,
    mut v_inst_1637_: *mut leanh::LeanObject,
    mut v_f_1638_: *mut leanh::LeanObject,
    mut v_init_1639_: *mut leanh::LeanObject,
    mut v_self_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1641_ = l_Lake_RBArray_foldrM(
        v_m_1632_,
        v_00_u03b2_1633_,
        v_00_u03c3_1634_,
        v_00_u03b1_1635_,
        v_cmp_1636_,
        v_inst_1637_,
        v_f_1638_,
        v_init_1639_,
        v_self_1640_,
    );
    leanh::lean_dec_ref(v_cmp_1636_);
    return v_res_1641_;
}
pub unsafe fn l_Lake_RBArray_forM___redArg___lam__0(
    mut v_f_1642_: *mut leanh::LeanObject,
    mut v_x_1643_: *mut leanh::LeanObject,
    mut v___y_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = leanh::lean_apply_1(v_f_1642_, v___y_1644_);
    return v___x_1645_;
}
pub unsafe fn l_Lake_RBArray_forM___redArg(
    mut v_inst_1646_: *mut leanh::LeanObject,
    mut v_f_1647_: *mut leanh::LeanObject,
    mut v_self_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    v_toArray_1649_ = leanh::lean_ctor_get(v_self_1648_, 1);
    leanh::lean_inc_ref(v_toArray_1649_);
    leanh::lean_dec_ref(v_self_1648_);
    v___x_1650_ = leanh::lean_unsigned_to_nat(0);
    v___x_1651_ = lean_array_get_size(v_toArray_1649_);
    v___x_1652_ = leanh::lean_box(0);
    v___x_1653_ = lean_nat_dec_lt(v___x_1650_, v___x_1651_);
    if v___x_1653_ == 0 {
        let mut v_toApplicative_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1649_);
        leanh::lean_dec(v_f_1647_);
        v_toApplicative_1654_ = leanh::lean_ctor_get(v_inst_1646_, 0);
        leanh::lean_inc_ref(v_toApplicative_1654_);
        leanh::lean_dec_ref(v_inst_1646_);
        v_toPure_1655_ = leanh::lean_ctor_get(v_toApplicative_1654_, 1);
        leanh::lean_inc(v_toPure_1655_);
        leanh::lean_dec_ref(v_toApplicative_1654_);
        v___x_1656_ =
            leanh::lean_apply_2(v_toPure_1655_, leanh::lean_box(0), v___x_1652_);
        return v___x_1656_;
    } else {
        let mut v___f_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1658_: u8 = 0;
        v___f_1657_ = leanh::lean_alloc_closure(
            l_Lake_RBArray_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1657_, 0, v_f_1647_);
        v___x_1658_ = lean_nat_dec_le(v___x_1651_, v___x_1651_);
        if v___x_1658_ == 0 {
            if v___x_1653_ == 0 {
                let mut v_toApplicative_1659_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_1657_);
                leanh::lean_dec_ref(v_toArray_1649_);
                v_toApplicative_1659_ = leanh::lean_ctor_get(v_inst_1646_, 0);
                leanh::lean_inc_ref(v_toApplicative_1659_);
                leanh::lean_dec_ref(v_inst_1646_);
                v_toPure_1660_ = leanh::lean_ctor_get(v_toApplicative_1659_, 1);
                leanh::lean_inc(v_toPure_1660_);
                leanh::lean_dec_ref(v_toApplicative_1659_);
                v___x_1661_ = leanh::lean_apply_2(
                    v_toPure_1660_,
                    leanh::lean_box(0),
                    v___x_1652_,
                );
                return v___x_1661_;
            } else {
                let mut v___x_1662_: usize = 0;
                let mut v___x_1663_: usize = 0;
                let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1662_ = 0usize;
                v___x_1663_ = lean_usize_of_nat(v___x_1651_);
                v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1646_,
                    v___f_1657_,
                    v_toArray_1649_,
                    v___x_1662_,
                    v___x_1663_,
                    v___x_1652_,
                );
                return v___x_1664_;
            }
        } else {
            let mut v___x_1665_: usize = 0;
            let mut v___x_1666_: usize = 0;
            let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1665_ = 0usize;
            v___x_1666_ = lean_usize_of_nat(v___x_1651_);
            v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1646_,
                v___f_1657_,
                v_toArray_1649_,
                v___x_1665_,
                v___x_1666_,
                v___x_1652_,
            );
            return v___x_1667_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_forM(
    mut v_m_1668_: *mut leanh::LeanObject,
    mut v_00_u03b2_1669_: *mut leanh::LeanObject,
    mut v_00_u03b1_1670_: *mut leanh::LeanObject,
    mut v_cmp_1671_: *mut leanh::LeanObject,
    mut v_inst_1672_: *mut leanh::LeanObject,
    mut v_f_1673_: *mut leanh::LeanObject,
    mut v_self_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    v_toArray_1675_ = leanh::lean_ctor_get(v_self_1674_, 1);
    leanh::lean_inc_ref(v_toArray_1675_);
    leanh::lean_dec_ref(v_self_1674_);
    v___x_1676_ = leanh::lean_unsigned_to_nat(0);
    v___x_1677_ = lean_array_get_size(v_toArray_1675_);
    v___x_1678_ = leanh::lean_box(0);
    v___x_1679_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
    if v___x_1679_ == 0 {
        let mut v_toApplicative_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1675_);
        leanh::lean_dec(v_f_1673_);
        v_toApplicative_1680_ = leanh::lean_ctor_get(v_inst_1672_, 0);
        leanh::lean_inc_ref(v_toApplicative_1680_);
        leanh::lean_dec_ref(v_inst_1672_);
        v_toPure_1681_ = leanh::lean_ctor_get(v_toApplicative_1680_, 1);
        leanh::lean_inc(v_toPure_1681_);
        leanh::lean_dec_ref(v_toApplicative_1680_);
        v___x_1682_ =
            leanh::lean_apply_2(v_toPure_1681_, leanh::lean_box(0), v___x_1678_);
        return v___x_1682_;
    } else {
        let mut v___f_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: u8 = 0;
        v___f_1683_ = leanh::lean_alloc_closure(
            l_Lake_RBArray_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1683_, 0, v_f_1673_);
        v___x_1684_ = lean_nat_dec_le(v___x_1677_, v___x_1677_);
        if v___x_1684_ == 0 {
            if v___x_1679_ == 0 {
                let mut v_toApplicative_1685_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_1683_);
                leanh::lean_dec_ref(v_toArray_1675_);
                v_toApplicative_1685_ = leanh::lean_ctor_get(v_inst_1672_, 0);
                leanh::lean_inc_ref(v_toApplicative_1685_);
                leanh::lean_dec_ref(v_inst_1672_);
                v_toPure_1686_ = leanh::lean_ctor_get(v_toApplicative_1685_, 1);
                leanh::lean_inc(v_toPure_1686_);
                leanh::lean_dec_ref(v_toApplicative_1685_);
                v___x_1687_ = leanh::lean_apply_2(
                    v_toPure_1686_,
                    leanh::lean_box(0),
                    v___x_1678_,
                );
                return v___x_1687_;
            } else {
                let mut v___x_1688_: usize = 0;
                let mut v___x_1689_: usize = 0;
                let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1688_ = 0usize;
                v___x_1689_ = lean_usize_of_nat(v___x_1677_);
                v___x_1690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1672_,
                    v___f_1683_,
                    v_toArray_1675_,
                    v___x_1688_,
                    v___x_1689_,
                    v___x_1678_,
                );
                return v___x_1690_;
            }
        } else {
            let mut v___x_1691_: usize = 0;
            let mut v___x_1692_: usize = 0;
            let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1691_ = 0usize;
            v___x_1692_ = lean_usize_of_nat(v___x_1677_);
            v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1672_,
                v___f_1683_,
                v_toArray_1675_,
                v___x_1691_,
                v___x_1692_,
                v___x_1678_,
            );
            return v___x_1693_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_forM___boxed(
    mut v_m_1694_: *mut leanh::LeanObject,
    mut v_00_u03b2_1695_: *mut leanh::LeanObject,
    mut v_00_u03b1_1696_: *mut leanh::LeanObject,
    mut v_cmp_1697_: *mut leanh::LeanObject,
    mut v_inst_1698_: *mut leanh::LeanObject,
    mut v_f_1699_: *mut leanh::LeanObject,
    mut v_self_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lake_RBArray_forM(
        v_m_1694_,
        v_00_u03b2_1695_,
        v_00_u03b1_1696_,
        v_cmp_1697_,
        v_inst_1698_,
        v_f_1699_,
        v_self_1700_,
    );
    leanh::lean_dec_ref(v_cmp_1697_);
    return v_res_1701_;
}
pub unsafe fn l_Lake_RBArray_forIn___redArg___lam__0(
    mut v_f_1702_: *mut leanh::LeanObject,
    mut v_a_1703_: *mut leanh::LeanObject,
    mut v_x_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = leanh::lean_apply_2(v_f_1702_, v_a_1703_, v___y_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Lake_RBArray_forIn___redArg(
    mut v_inst_1707_: *mut leanh::LeanObject,
    mut v_self_1708_: *mut leanh::LeanObject,
    mut v_init_1709_: *mut leanh::LeanObject,
    mut v_f_1710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1713_: usize = 0;
    let mut v___x_1714_: usize = 0;
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toArray_1711_ = leanh::lean_ctor_get(v_self_1708_, 1);
    leanh::lean_inc_ref(v_toArray_1711_);
    leanh::lean_dec_ref(v_self_1708_);
    v___f_1712_ = leanh::lean_alloc_closure(
        l_Lake_RBArray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1712_, 0, v_f_1710_);
    v_sz_1713_ = lean_array_size(v_toArray_1711_);
    v___x_1714_ = 0usize;
    v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1707_,
        v_toArray_1711_,
        v___f_1712_,
        v_sz_1713_,
        v___x_1714_,
        v_init_1709_,
    );
    return v___x_1715_;
}
pub unsafe fn l_Lake_RBArray_forIn(
    mut v_m_1716_: *mut leanh::LeanObject,
    mut v_00_u03b1_1717_: *mut leanh::LeanObject,
    mut v_00_u03b2_1718_: *mut leanh::LeanObject,
    mut v_cmp_1719_: *mut leanh::LeanObject,
    mut v_00_u03c3_1720_: *mut leanh::LeanObject,
    mut v_inst_1721_: *mut leanh::LeanObject,
    mut v_self_1722_: *mut leanh::LeanObject,
    mut v_init_1723_: *mut leanh::LeanObject,
    mut v_f_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1727_: usize = 0;
    let mut v___x_1728_: usize = 0;
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toArray_1725_ = leanh::lean_ctor_get(v_self_1722_, 1);
    leanh::lean_inc_ref(v_toArray_1725_);
    leanh::lean_dec_ref(v_self_1722_);
    v___f_1726_ = leanh::lean_alloc_closure(
        l_Lake_RBArray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1726_, 0, v_f_1724_);
    v_sz_1727_ = lean_array_size(v_toArray_1725_);
    v___x_1728_ = 0usize;
    v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1721_,
        v_toArray_1725_,
        v___f_1726_,
        v_sz_1727_,
        v___x_1728_,
        v_init_1723_,
    );
    return v___x_1729_;
}
pub unsafe fn l_Lake_RBArray_forIn___boxed(
    mut v_m_1730_: *mut leanh::LeanObject,
    mut v_00_u03b1_1731_: *mut leanh::LeanObject,
    mut v_00_u03b2_1732_: *mut leanh::LeanObject,
    mut v_cmp_1733_: *mut leanh::LeanObject,
    mut v_00_u03c3_1734_: *mut leanh::LeanObject,
    mut v_inst_1735_: *mut leanh::LeanObject,
    mut v_self_1736_: *mut leanh::LeanObject,
    mut v_init_1737_: *mut leanh::LeanObject,
    mut v_f_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1739_ = l_Lake_RBArray_forIn(
        v_m_1730_,
        v_00_u03b1_1731_,
        v_00_u03b2_1732_,
        v_cmp_1733_,
        v_00_u03c3_1734_,
        v_inst_1735_,
        v_self_1736_,
        v_init_1737_,
        v_f_1738_,
    );
    leanh::lean_dec_ref(v_cmp_1733_);
    return v_res_1739_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0(
    mut v___y_1740_: *mut leanh::LeanObject,
    mut v_a_1741_: *mut leanh::LeanObject,
    mut v_x_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = leanh::lean_apply_2(v___y_1740_, v_a_1741_, v___y_1743_);
    return v___x_1744_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1(
    mut v_inst_1745_: *mut leanh::LeanObject,
    mut v_00_u03b2_1746_: *mut leanh::LeanObject,
    mut v___y_1747_: *mut leanh::LeanObject,
    mut v___y_1748_: *mut leanh::LeanObject,
    mut v___y_1749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1752_: usize = 0;
    let mut v___x_1753_: usize = 0;
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toArray_1750_ = leanh::lean_ctor_get(v___y_1747_, 1);
    leanh::lean_inc_ref(v_toArray_1750_);
    leanh::lean_dec_ref(v___y_1747_);
    v___f_1751_ = leanh::lean_alloc_closure(
        l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1751_, 0, v___y_1749_);
    v_sz_1752_ = lean_array_size(v_toArray_1750_);
    v___x_1753_ = 0usize;
    v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1745_,
        v_toArray_1750_,
        v___f_1751_,
        v_sz_1752_,
        v___x_1753_,
        v___y_1748_,
    );
    return v___x_1754_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg(
    mut v_inst_1755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1756_ = leanh::lean_alloc_closure(
        l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1756_, 0, v_inst_1755_);
    return v___f_1756_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(
    mut v_m_1757_: *mut leanh::LeanObject,
    mut v_00_u03b1_1758_: *mut leanh::LeanObject,
    mut v_00_u03b2_1759_: *mut leanh::LeanObject,
    mut v_cmp_1760_: *mut leanh::LeanObject,
    mut v_inst_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1762_ = leanh::lean_alloc_closure(
        l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1762_, 0, v_inst_1761_);
    return v___f_1762_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___boxed(
    mut v_m_1763_: *mut leanh::LeanObject,
    mut v_00_u03b1_1764_: *mut leanh::LeanObject,
    mut v_00_u03b2_1765_: *mut leanh::LeanObject,
    mut v_cmp_1766_: *mut leanh::LeanObject,
    mut v_inst_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(
        v_m_1763_,
        v_00_u03b1_1764_,
        v_00_u03b2_1765_,
        v_cmp_1766_,
        v_inst_1767_,
    );
    leanh::lean_dec_ref(v_cmp_1766_);
    return v_res_1768_;
}
pub unsafe fn l_Lake_mkRBArray___redArg___lam__0(
    mut v_f_1769_: *mut leanh::LeanObject,
    mut v_cmp_1770_: *mut leanh::LeanObject,
    mut v_x1_1771_: *mut leanh::LeanObject,
    mut v_x2_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_x2_1772_);
    v___x_1773_ = leanh::lean_apply_1(v_f_1769_, v_x2_1772_);
    v___x_1774_ = l_Lake_RBArray_insert___redArg(v_cmp_1770_, v_x1_1771_, v___x_1773_, v_x2_1772_);
    return v___x_1774_;
}
pub unsafe fn l_Lake_mkRBArray___redArg(
    mut v_cmp_1775_: *mut leanh::LeanObject,
    mut v_f_1776_: *mut leanh::LeanObject,
    mut v_vs_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    v___x_1778_ = lean_array_get_size(v_vs_1777_);
    v___x_1779_ = l_Lake_RBArray_mkEmpty___redArg(v___x_1778_);
    v___x_1780_ = leanh::lean_unsigned_to_nat(0);
    v___x_1781_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1782_ = lean_nat_dec_lt(v___x_1780_, v___x_1778_);
    if v___x_1782_ == 0 {
        leanh::lean_dec_ref(v_vs_1777_);
        leanh::lean_dec(v_f_1776_);
        leanh::lean_dec_ref(v_cmp_1775_);
        return v___x_1779_;
    } else {
        let mut v___f_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1784_: u8 = 0;
        v___f_1783_ = leanh::lean_alloc_closure(
            l_Lake_mkRBArray___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_1783_, 0, v_f_1776_);
        leanh::lean_closure_set(v___f_1783_, 1, v_cmp_1775_);
        v___x_1784_ = lean_nat_dec_le(v___x_1778_, v___x_1778_);
        if v___x_1784_ == 0 {
            if v___x_1782_ == 0 {
                leanh::lean_dec_ref(v___f_1783_);
                leanh::lean_dec_ref(v_vs_1777_);
                return v___x_1779_;
            } else {
                let mut v___x_1785_: usize = 0;
                let mut v___x_1786_: usize = 0;
                let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1785_ = 0usize;
                v___x_1786_ = lean_usize_of_nat(v___x_1778_);
                v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1781_,
                    v___f_1783_,
                    v_vs_1777_,
                    v___x_1785_,
                    v___x_1786_,
                    v___x_1779_,
                );
                return v___x_1787_;
            }
        } else {
            let mut v___x_1788_: usize = 0;
            let mut v___x_1789_: usize = 0;
            let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1788_ = 0usize;
            v___x_1789_ = lean_usize_of_nat(v___x_1778_);
            v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1781_,
                v___f_1783_,
                v_vs_1777_,
                v___x_1788_,
                v___x_1789_,
                v___x_1779_,
            );
            return v___x_1790_;
        }
    }
}
pub unsafe fn l_Lake_mkRBArray(
    mut v_00_u03b2_1791_: *mut leanh::LeanObject,
    mut v_00_u03b1_1792_: *mut leanh::LeanObject,
    mut v_cmp_1793_: *mut leanh::LeanObject,
    mut v_f_1794_: *mut leanh::LeanObject,
    mut v_vs_1795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    v___x_1796_ = lean_array_get_size(v_vs_1795_);
    v___x_1797_ = l_Lake_RBArray_mkEmpty___redArg(v___x_1796_);
    v___x_1798_ = leanh::lean_unsigned_to_nat(0);
    v___x_1799_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1800_ = lean_nat_dec_lt(v___x_1798_, v___x_1796_);
    if v___x_1800_ == 0 {
        leanh::lean_dec_ref(v_vs_1795_);
        leanh::lean_dec(v_f_1794_);
        leanh::lean_dec_ref(v_cmp_1793_);
        return v___x_1797_;
    } else {
        let mut v___f_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: u8 = 0;
        v___f_1801_ = leanh::lean_alloc_closure(
            l_Lake_mkRBArray___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_1801_, 0, v_f_1794_);
        leanh::lean_closure_set(v___f_1801_, 1, v_cmp_1793_);
        v___x_1802_ = lean_nat_dec_le(v___x_1796_, v___x_1796_);
        if v___x_1802_ == 0 {
            if v___x_1800_ == 0 {
                leanh::lean_dec_ref(v___f_1801_);
                leanh::lean_dec_ref(v_vs_1795_);
                return v___x_1797_;
            } else {
                let mut v___x_1803_: usize = 0;
                let mut v___x_1804_: usize = 0;
                let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1803_ = 0usize;
                v___x_1804_ = lean_usize_of_nat(v___x_1796_);
                v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1799_,
                    v___f_1801_,
                    v_vs_1795_,
                    v___x_1803_,
                    v___x_1804_,
                    v___x_1797_,
                );
                return v___x_1805_;
            }
        } else {
            let mut v___x_1806_: usize = 0;
            let mut v___x_1807_: usize = 0;
            let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1806_ = 0usize;
            v___x_1807_ = lean_usize_of_nat(v___x_1796_);
            v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1799_,
                v___f_1801_,
                v_vs_1795_,
                v___x_1806_,
                v___x_1807_,
                v___x_1797_,
            );
            return v___x_1808_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_RBArray(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_RBArray(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_RBArray(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_RBArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_RBArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_RBArray(builtin);
}