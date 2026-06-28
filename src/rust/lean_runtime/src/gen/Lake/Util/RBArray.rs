// Lean compiler output
// Module: Lake.Util.RBArray
// Imports: Std.Data.TreeMap.Basic
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Lake_RBArray_empty___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_RBArray_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_empty___closed__0_value) as *mut LeanObject;
pub static l_Lake_RBArray_empty___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_RBArray_empty___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_RBArray_empty___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_empty___closed__1_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lake_RBArray_all___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_RBArray_all___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_RBArray_all___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lake_RBArray_all___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_RBArray_all___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_RBArray_all___redArg___closed__9_value) as *mut LeanObject;
pub unsafe fn l_Lake_RBArray_empty(
    mut v_00_u03b1_910_: *mut LeanObject,
    mut v_00_u03b2_911_: *mut LeanObject,
    mut v_cmp_912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lake_RBArray_empty___closed__1;
    return v___x_913_;
}
pub unsafe fn l_Lake_RBArray_empty___boxed(
    mut v_00_u03b1_914_: *mut LeanObject,
    mut v_00_u03b2_915_: *mut LeanObject,
    mut v_cmp_916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_917_: *mut LeanObject = core::ptr::null_mut();
    v_res_917_ = l_Lake_RBArray_empty(v_00_u03b1_914_, v_00_u03b2_915_, v_cmp_916_);
    lean_dec_ref(v_cmp_916_);
    return v_res_917_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(
    mut v_cmp_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    v___x_919_ = l_Lake_RBArray_empty(lean_box(0), lean_box(0), v_cmp_918_);
    return v___x_919_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg___boxed(
    mut v_cmp_920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_921_: *mut LeanObject = core::ptr::null_mut();
    v_res_921_ =
        l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(v_cmp_920_);
    lean_dec_ref(v_cmp_920_);
    return v_res_921_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(
    mut v_00_u03b1_922_: *mut LeanObject,
    mut v_00_u03b2_923_: *mut LeanObject,
    mut v_cmp_924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Lake_RBArray_empty(lean_box(0), lean_box(0), v_cmp_924_);
    return v___x_925_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___boxed(
    mut v_00_u03b1_926_: *mut LeanObject,
    mut v_00_u03b2_927_: *mut LeanObject,
    mut v_cmp_928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_929_: *mut LeanObject = core::ptr::null_mut();
    v_res_929_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(
        v_00_u03b1_926_,
        v_00_u03b2_927_,
        v_cmp_928_,
    );
    lean_dec_ref(v_cmp_928_);
    return v_res_929_;
}
pub unsafe fn l_Lake_RBArray_mkEmpty___redArg(mut v_size_930_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    v___x_931_ = lean_box(1);
    v___x_932_ = lean_mk_empty_array_with_capacity(v_size_930_);
    v___x_933_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_933_, 0, v___x_931_);
    lean_ctor_set(v___x_933_, 1, v___x_932_);
    return v___x_933_;
}
pub unsafe fn l_Lake_RBArray_mkEmpty___redArg___boxed(
    mut v_size_934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_935_: *mut LeanObject = core::ptr::null_mut();
    v_res_935_ = l_Lake_RBArray_mkEmpty___redArg(v_size_934_);
    lean_dec(v_size_934_);
    return v_res_935_;
}
pub unsafe fn l_Lake_RBArray_mkEmpty(
    mut v_00_u03b1_936_: *mut LeanObject,
    mut v_00_u03b2_937_: *mut LeanObject,
    mut v_cmp_938_: *mut LeanObject,
    mut v_size_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    v___x_940_ = l_Lake_RBArray_mkEmpty___redArg(v_size_939_);
    return v___x_940_;
}
pub unsafe fn l_Lake_RBArray_mkEmpty___boxed(
    mut v_00_u03b1_941_: *mut LeanObject,
    mut v_00_u03b2_942_: *mut LeanObject,
    mut v_cmp_943_: *mut LeanObject,
    mut v_size_944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_945_: *mut LeanObject = core::ptr::null_mut();
    v_res_945_ = l_Lake_RBArray_mkEmpty(v_00_u03b1_941_, v_00_u03b2_942_, v_cmp_943_, v_size_944_);
    lean_dec(v_size_944_);
    lean_dec_ref(v_cmp_943_);
    return v_res_945_;
}
pub unsafe fn l_Lake_RBArray_find_x3f___redArg(
    mut v_cmp_946_: *mut LeanObject,
    mut v_self_947_: *mut LeanObject,
    mut v_a_948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toTreeMap_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v_toTreeMap_949_ = lean_ctor_get(v_self_947_, 0);
    lean_inc(v_toTreeMap_949_);
    lean_dec_ref(v_self_947_);
    v___x_950_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_946_, v_toTreeMap_949_, v_a_948_);
    return v___x_950_;
}
pub unsafe fn l_Lake_RBArray_find_x3f(
    mut v_00_u03b1_951_: *mut LeanObject,
    mut v_00_u03b2_952_: *mut LeanObject,
    mut v_cmp_953_: *mut LeanObject,
    mut v_self_954_: *mut LeanObject,
    mut v_a_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toTreeMap_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v_toTreeMap_956_ = lean_ctor_get(v_self_954_, 0);
    lean_inc(v_toTreeMap_956_);
    lean_dec_ref(v_self_954_);
    v___x_957_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_953_, v_toTreeMap_956_, v_a_955_);
    return v___x_957_;
}
pub unsafe fn l_Lake_RBArray_contains___redArg(
    mut v_cmp_958_: *mut LeanObject,
    mut v_self_959_: *mut LeanObject,
    mut v_a_960_: *mut LeanObject,
) -> u8 {
    let mut v_toTreeMap_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    v_toTreeMap_961_ = lean_ctor_get(v_self_959_, 0);
    lean_inc(v_toTreeMap_961_);
    lean_dec_ref(v_self_959_);
    v___x_962_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_958_, v_a_960_, v_toTreeMap_961_);
    return v___x_962_;
}
pub unsafe fn l_Lake_RBArray_contains___redArg___boxed(
    mut v_cmp_963_: *mut LeanObject,
    mut v_self_964_: *mut LeanObject,
    mut v_a_965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_966_: u8 = 0;
    let mut v_r_967_: *mut LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lake_RBArray_contains___redArg(v_cmp_963_, v_self_964_, v_a_965_);
    v_r_967_ = lean_box((v_res_966_) as usize);
    return v_r_967_;
}
pub unsafe fn l_Lake_RBArray_contains(
    mut v_00_u03b1_968_: *mut LeanObject,
    mut v_00_u03b2_969_: *mut LeanObject,
    mut v_cmp_970_: *mut LeanObject,
    mut v_self_971_: *mut LeanObject,
    mut v_a_972_: *mut LeanObject,
) -> u8 {
    let mut v_toTreeMap_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    v_toTreeMap_973_ = lean_ctor_get(v_self_971_, 0);
    lean_inc(v_toTreeMap_973_);
    lean_dec_ref(v_self_971_);
    v___x_974_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_970_, v_a_972_, v_toTreeMap_973_);
    return v___x_974_;
}
pub unsafe fn l_Lake_RBArray_contains___boxed(
    mut v_00_u03b1_975_: *mut LeanObject,
    mut v_00_u03b2_976_: *mut LeanObject,
    mut v_cmp_977_: *mut LeanObject,
    mut v_self_978_: *mut LeanObject,
    mut v_a_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_980_: u8 = 0;
    let mut v_r_981_: *mut LeanObject = core::ptr::null_mut();
    v_res_980_ = l_Lake_RBArray_contains(
        v_00_u03b1_975_,
        v_00_u03b2_976_,
        v_cmp_977_,
        v_self_978_,
        v_a_979_,
    );
    v_r_981_ = lean_box((v_res_980_) as usize);
    return v_r_981_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(
    mut v_cmp_982_: *mut LeanObject,
    mut v_k_983_: *mut LeanObject,
    mut v_v_984_: *mut LeanObject,
    mut v_t_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_993_: u8 = 0;
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: u8 = 0;
    let mut v_impl_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1014_: u8 = 0;
    let mut v_size_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1026_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v_unused_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1070_: u8 = 0;
    let mut v_unused_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut v_unused_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1089_: u8 = 0;
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut v_unused_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v_k_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1121_: u8 = 0;
    let mut v_unused_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_unused_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: u8 = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v_size_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut v_unused_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1204_: u8 = 0;
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1208_: u8 = 0;
    let mut v_unused_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1215_: u8 = 0;
    let mut v_unused_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v_k_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1243_: u8 = 0;
    let mut v_unused_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut v_unused_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1255_: u8 = 0;
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut v_unused_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_985_) == 0 {
                    v_size_986_ = lean_ctor_get(v_t_985_, 0);
                    v_k_987_ = lean_ctor_get(v_t_985_, 1);
                    v_v_988_ = lean_ctor_get(v_t_985_, 2);
                    v_l_989_ = lean_ctor_get(v_t_985_, 3);
                    v_r_990_ = lean_ctor_get(v_t_985_, 4);
                    v_isSharedCheck_1271_ = (!lean_is_exclusive(v_t_985_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_992_ = v_t_985_;
                        v_isShared_993_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_990_);
                        lean_inc(v_l_989_);
                        lean_inc(v_v_988_);
                        lean_inc(v_k_987_);
                        lean_inc(v_size_986_);
                        lean_dec(v_t_985_);
                        v___x_992_ = lean_box(0);
                        v_isShared_993_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_cmp_982_);
                    v___x_1272_ = lean_unsigned_to_nat(1);
                    v___x_1273_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_1273_, 0, v___x_1272_);
                    lean_ctor_set(v___x_1273_, 1, v_k_983_);
                    lean_ctor_set(v___x_1273_, 2, v_v_984_);
                    lean_ctor_set(v___x_1273_, 3, v_t_985_);
                    lean_ctor_set(v___x_1273_, 4, v_t_985_);
                    return v___x_1273_;
                }
            }
            1 => {
                lean_inc_ref(v_cmp_982_);
                lean_inc(v_k_987_);
                lean_inc(v_k_983_);
                v___x_994_ = lean_apply_2(v_cmp_982_, v_k_983_, v_k_987_);
                v___x_995_ = (lean_unbox(v___x_994_) as u8);
                match v___x_995_ {
                    0 => {
                        lean_dec(v_size_986_);
                        v_impl_996_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_982_, v_k_983_, v_v_984_, v_l_989_);
                        v___x_997_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_990_) == 0 {
                            v_size_998_ = lean_ctor_get(v_r_990_, 0);
                            v_size_999_ = lean_ctor_get(v_impl_996_, 0);
                            lean_inc(v_size_999_);
                            v_k_1000_ = lean_ctor_get(v_impl_996_, 1);
                            lean_inc(v_k_1000_);
                            v_v_1001_ = lean_ctor_get(v_impl_996_, 2);
                            lean_inc(v_v_1001_);
                            v_l_1002_ = lean_ctor_get(v_impl_996_, 3);
                            lean_inc(v_l_1002_);
                            v_r_1003_ = lean_ctor_get(v_impl_996_, 4);
                            lean_inc(v_r_1003_);
                            v___x_1004_ = lean_unsigned_to_nat(3);
                            v___x_1005_ = lean_nat_mul(v___x_1004_, v_size_998_);
                            v___x_1006_ = lean_nat_dec_lt(v___x_1005_, v_size_999_);
                            lean_dec(v___x_1005_);
                            if v___x_1006_ == 0 {
                                lean_dec(v_r_1003_);
                                lean_dec(v_l_1002_);
                                lean_dec(v_v_1001_);
                                lean_dec(v_k_1000_);
                                v___x_1007_ = lean_nat_add(v___x_997_, v_size_999_);
                                lean_dec(v_size_999_);
                                v___x_1008_ = lean_nat_add(v___x_1007_, v_size_998_);
                                lean_dec(v___x_1007_);
                                if v_isShared_993_ == 0 {
                                    lean_ctor_set(v___x_992_, 3, v_impl_996_);
                                    lean_ctor_set(v___x_992_, 0, v___x_1008_);
                                    v___x_1010_ = v___x_992_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
                                    lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_987_);
                                    lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_v_988_);
                                    lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_impl_996_);
                                    lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_r_990_);
                                    v___x_1010_ = v_reuseFailAlloc_1011_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1077_ = (!lean_is_exclusive(v_impl_996_)) as u8;
                                if v_isSharedCheck_1077_ == 0 {
                                    v_unused_1078_ = lean_ctor_get(v_impl_996_, 4);
                                    lean_dec(v_unused_1078_);
                                    v_unused_1079_ = lean_ctor_get(v_impl_996_, 3);
                                    lean_dec(v_unused_1079_);
                                    v_unused_1080_ = lean_ctor_get(v_impl_996_, 2);
                                    lean_dec(v_unused_1080_);
                                    v_unused_1081_ = lean_ctor_get(v_impl_996_, 1);
                                    lean_dec(v_unused_1081_);
                                    v_unused_1082_ = lean_ctor_get(v_impl_996_, 0);
                                    lean_dec(v_unused_1082_);
                                    v___x_1013_ = v_impl_996_;
                                    v_isShared_1014_ = v_isSharedCheck_1077_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_996_);
                                    v___x_1013_ = lean_box(0);
                                    v_isShared_1014_ = v_isSharedCheck_1077_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1083_ = lean_ctor_get(v_impl_996_, 3);
                            lean_inc(v_l_1083_);
                            if lean_obj_tag(v_l_1083_) == 0 {
                                v_r_1084_ = lean_ctor_get(v_impl_996_, 4);
                                v_k_1085_ = lean_ctor_get(v_impl_996_, 1);
                                v_v_1086_ = lean_ctor_get(v_impl_996_, 2);
                                v_isSharedCheck_1097_ = (!lean_is_exclusive(v_impl_996_)) as u8;
                                if v_isSharedCheck_1097_ == 0 {
                                    v_unused_1098_ = lean_ctor_get(v_impl_996_, 3);
                                    lean_dec(v_unused_1098_);
                                    v_unused_1099_ = lean_ctor_get(v_impl_996_, 0);
                                    lean_dec(v_unused_1099_);
                                    v___x_1088_ = v_impl_996_;
                                    v_isShared_1089_ = v_isSharedCheck_1097_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_1084_);
                                    lean_inc(v_v_1086_);
                                    lean_inc(v_k_1085_);
                                    lean_dec(v_impl_996_);
                                    v___x_1088_ = lean_box(0);
                                    v_isShared_1089_ = v_isSharedCheck_1097_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1100_ = lean_ctor_get(v_impl_996_, 4);
                                lean_inc(v_r_1100_);
                                if lean_obj_tag(v_r_1100_) == 0 {
                                    v_k_1101_ = lean_ctor_get(v_impl_996_, 1);
                                    v_v_1102_ = lean_ctor_get(v_impl_996_, 2);
                                    v_isSharedCheck_1125_ = (!lean_is_exclusive(v_impl_996_)) as u8;
                                    if v_isSharedCheck_1125_ == 0 {
                                        v_unused_1126_ = lean_ctor_get(v_impl_996_, 4);
                                        lean_dec(v_unused_1126_);
                                        v_unused_1127_ = lean_ctor_get(v_impl_996_, 3);
                                        lean_dec(v_unused_1127_);
                                        v_unused_1128_ = lean_ctor_get(v_impl_996_, 0);
                                        lean_dec(v_unused_1128_);
                                        v___x_1104_ = v_impl_996_;
                                        v_isShared_1105_ = v_isSharedCheck_1125_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1102_);
                                        lean_inc(v_k_1101_);
                                        lean_dec(v_impl_996_);
                                        v___x_1104_ = lean_box(0);
                                        v_isShared_1105_ = v_isSharedCheck_1125_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1129_ = lean_unsigned_to_nat(2);
                                    if v_isShared_993_ == 0 {
                                        lean_ctor_set(v___x_992_, 4, v_r_1100_);
                                        lean_ctor_set(v___x_992_, 3, v_impl_996_);
                                        lean_ctor_set(v___x_992_, 0, v___x_1129_);
                                        v___x_1131_ = v___x_992_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
                                        lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_k_987_);
                                        lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_v_988_);
                                        lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_impl_996_);
                                        lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_r_1100_);
                                        v___x_1131_ = v_reuseFailAlloc_1132_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_988_);
                        lean_dec(v_k_987_);
                        lean_dec_ref(v_cmp_982_);
                        if v_isShared_993_ == 0 {
                            lean_ctor_set(v___x_992_, 2, v_v_984_);
                            lean_ctor_set(v___x_992_, 1, v_k_983_);
                            v___x_1134_ = v___x_992_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_size_986_);
                            lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_983_);
                            lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_984_);
                            lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_l_989_);
                            lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_r_990_);
                            v___x_1134_ = v_reuseFailAlloc_1135_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_986_);
                        v_impl_1136_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_982_, v_k_983_, v_v_984_, v_r_990_);
                        v___x_1137_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_989_) == 0 {
                            v_size_1138_ = lean_ctor_get(v_l_989_, 0);
                            v_size_1139_ = lean_ctor_get(v_impl_1136_, 0);
                            lean_inc(v_size_1139_);
                            v_k_1140_ = lean_ctor_get(v_impl_1136_, 1);
                            lean_inc(v_k_1140_);
                            v_v_1141_ = lean_ctor_get(v_impl_1136_, 2);
                            lean_inc(v_v_1141_);
                            v_l_1142_ = lean_ctor_get(v_impl_1136_, 3);
                            lean_inc(v_l_1142_);
                            v_r_1143_ = lean_ctor_get(v_impl_1136_, 4);
                            lean_inc(v_r_1143_);
                            v___x_1144_ = lean_unsigned_to_nat(3);
                            v___x_1145_ = lean_nat_mul(v___x_1144_, v_size_1138_);
                            v___x_1146_ = lean_nat_dec_lt(v___x_1145_, v_size_1139_);
                            lean_dec(v___x_1145_);
                            if v___x_1146_ == 0 {
                                lean_dec(v_r_1143_);
                                lean_dec(v_l_1142_);
                                lean_dec(v_v_1141_);
                                lean_dec(v_k_1140_);
                                v___x_1147_ = lean_nat_add(v___x_1137_, v_size_1138_);
                                v___x_1148_ = lean_nat_add(v___x_1147_, v_size_1139_);
                                lean_dec(v_size_1139_);
                                lean_dec(v___x_1147_);
                                if v_isShared_993_ == 0 {
                                    lean_ctor_set(v___x_992_, 4, v_impl_1136_);
                                    lean_ctor_set(v___x_992_, 0, v___x_1148_);
                                    v___x_1150_ = v___x_992_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
                                    lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_987_);
                                    lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_988_);
                                    lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_l_989_);
                                    lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_impl_1136_);
                                    v___x_1150_ = v_reuseFailAlloc_1151_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1215_ = (!lean_is_exclusive(v_impl_1136_)) as u8;
                                if v_isSharedCheck_1215_ == 0 {
                                    v_unused_1216_ = lean_ctor_get(v_impl_1136_, 4);
                                    lean_dec(v_unused_1216_);
                                    v_unused_1217_ = lean_ctor_get(v_impl_1136_, 3);
                                    lean_dec(v_unused_1217_);
                                    v_unused_1218_ = lean_ctor_get(v_impl_1136_, 2);
                                    lean_dec(v_unused_1218_);
                                    v_unused_1219_ = lean_ctor_get(v_impl_1136_, 1);
                                    lean_dec(v_unused_1219_);
                                    v_unused_1220_ = lean_ctor_get(v_impl_1136_, 0);
                                    lean_dec(v_unused_1220_);
                                    v___x_1153_ = v_impl_1136_;
                                    v_isShared_1154_ = v_isSharedCheck_1215_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1136_);
                                    v___x_1153_ = lean_box(0);
                                    v_isShared_1154_ = v_isSharedCheck_1215_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1221_ = lean_ctor_get(v_impl_1136_, 3);
                            lean_inc(v_l_1221_);
                            if lean_obj_tag(v_l_1221_) == 0 {
                                v_r_1222_ = lean_ctor_get(v_impl_1136_, 4);
                                v_k_1223_ = lean_ctor_get(v_impl_1136_, 1);
                                v_v_1224_ = lean_ctor_get(v_impl_1136_, 2);
                                v_isSharedCheck_1247_ = (!lean_is_exclusive(v_impl_1136_)) as u8;
                                if v_isSharedCheck_1247_ == 0 {
                                    v_unused_1248_ = lean_ctor_get(v_impl_1136_, 3);
                                    lean_dec(v_unused_1248_);
                                    v_unused_1249_ = lean_ctor_get(v_impl_1136_, 0);
                                    lean_dec(v_unused_1249_);
                                    v___x_1226_ = v_impl_1136_;
                                    v_isShared_1227_ = v_isSharedCheck_1247_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_1222_);
                                    lean_inc(v_v_1224_);
                                    lean_inc(v_k_1223_);
                                    lean_dec(v_impl_1136_);
                                    v___x_1226_ = lean_box(0);
                                    v_isShared_1227_ = v_isSharedCheck_1247_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1250_ = lean_ctor_get(v_impl_1136_, 4);
                                lean_inc(v_r_1250_);
                                if lean_obj_tag(v_r_1250_) == 0 {
                                    v_k_1251_ = lean_ctor_get(v_impl_1136_, 1);
                                    v_v_1252_ = lean_ctor_get(v_impl_1136_, 2);
                                    v_isSharedCheck_1263_ =
                                        (!lean_is_exclusive(v_impl_1136_)) as u8;
                                    if v_isSharedCheck_1263_ == 0 {
                                        v_unused_1264_ = lean_ctor_get(v_impl_1136_, 4);
                                        lean_dec(v_unused_1264_);
                                        v_unused_1265_ = lean_ctor_get(v_impl_1136_, 3);
                                        lean_dec(v_unused_1265_);
                                        v_unused_1266_ = lean_ctor_get(v_impl_1136_, 0);
                                        lean_dec(v_unused_1266_);
                                        v___x_1254_ = v_impl_1136_;
                                        v_isShared_1255_ = v_isSharedCheck_1263_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1252_);
                                        lean_inc(v_k_1251_);
                                        lean_dec(v_impl_1136_);
                                        v___x_1254_ = lean_box(0);
                                        v_isShared_1255_ = v_isSharedCheck_1263_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1267_ = lean_unsigned_to_nat(2);
                                    if v_isShared_993_ == 0 {
                                        lean_ctor_set(v___x_992_, 4, v_impl_1136_);
                                        lean_ctor_set(v___x_992_, 3, v_r_1250_);
                                        lean_ctor_set(v___x_992_, 0, v___x_1267_);
                                        v___x_1269_ = v___x_992_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
                                        lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_k_987_);
                                        lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_v_988_);
                                        lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_r_1250_);
                                        lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_impl_1136_);
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
                v_size_1015_ = lean_ctor_get(v_l_1002_, 0);
                v_size_1016_ = lean_ctor_get(v_r_1003_, 0);
                v_k_1017_ = lean_ctor_get(v_r_1003_, 1);
                v_v_1018_ = lean_ctor_get(v_r_1003_, 2);
                v_l_1019_ = lean_ctor_get(v_r_1003_, 3);
                v_r_1020_ = lean_ctor_get(v_r_1003_, 4);
                v___x_1021_ = lean_unsigned_to_nat(2);
                v___x_1022_ = lean_nat_mul(v___x_1021_, v_size_1015_);
                v___x_1023_ = lean_nat_dec_lt(v_size_1016_, v___x_1022_);
                lean_dec(v___x_1022_);
                if v___x_1023_ == 0 {
                    lean_inc(v_r_1020_);
                    lean_inc(v_l_1019_);
                    lean_inc(v_v_1018_);
                    lean_inc(v_k_1017_);
                    v_isSharedCheck_1052_ = (!lean_is_exclusive(v_r_1003_)) as u8;
                    if v_isSharedCheck_1052_ == 0 {
                        v_unused_1053_ = lean_ctor_get(v_r_1003_, 4);
                        lean_dec(v_unused_1053_);
                        v_unused_1054_ = lean_ctor_get(v_r_1003_, 3);
                        lean_dec(v_unused_1054_);
                        v_unused_1055_ = lean_ctor_get(v_r_1003_, 2);
                        lean_dec(v_unused_1055_);
                        v_unused_1056_ = lean_ctor_get(v_r_1003_, 1);
                        lean_dec(v_unused_1056_);
                        v_unused_1057_ = lean_ctor_get(v_r_1003_, 0);
                        lean_dec(v_unused_1057_);
                        v___x_1025_ = v_r_1003_;
                        v_isShared_1026_ = v_isSharedCheck_1052_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_1003_);
                        v___x_1025_ = lean_box(0);
                        v_isShared_1026_ = v_isSharedCheck_1052_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_992_);
                    v___x_1058_ = lean_nat_add(v___x_997_, v_size_999_);
                    lean_dec(v_size_999_);
                    v___x_1059_ = lean_nat_add(v___x_1058_, v_size_998_);
                    lean_dec(v___x_1058_);
                    v___x_1060_ = lean_nat_add(v___x_997_, v_size_998_);
                    v___x_1061_ = lean_nat_add(v___x_1060_, v_size_1016_);
                    lean_dec(v___x_1060_);
                    lean_inc_ref(v_r_990_);
                    if v_isShared_1014_ == 0 {
                        lean_ctor_set(v___x_1013_, 4, v_r_990_);
                        lean_ctor_set(v___x_1013_, 3, v_r_1003_);
                        lean_ctor_set(v___x_1013_, 2, v_v_988_);
                        lean_ctor_set(v___x_1013_, 1, v_k_987_);
                        lean_ctor_set(v___x_1013_, 0, v___x_1061_);
                        v___x_1063_ = v___x_1013_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1061_);
                        lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_k_987_);
                        lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_v_988_);
                        lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_r_1003_);
                        lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_r_990_);
                        v___x_1063_ = v_reuseFailAlloc_1076_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1027_ = lean_nat_add(v___x_997_, v_size_999_);
                lean_dec(v_size_999_);
                v___x_1028_ = lean_nat_add(v___x_1027_, v_size_998_);
                lean_dec(v___x_1027_);
                v___x_1040_ = lean_nat_add(v___x_997_, v_size_1015_);
                if lean_obj_tag(v_l_1019_) == 0 {
                    v_size_1050_ = lean_ctor_get(v_l_1019_, 0);
                    lean_inc(v_size_1050_);
                    v___y_1042_ = v_size_1050_;
                    state = 8;
                    continue;
                } else {
                    v___x_1051_ = lean_unsigned_to_nat(0);
                    v___y_1042_ = v___x_1051_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1033_ = lean_nat_add(v___y_1031_, v___y_1032_);
                lean_dec(v___y_1032_);
                lean_dec(v___y_1031_);
                if v_isShared_1026_ == 0 {
                    lean_ctor_set(v___x_1025_, 4, v_r_990_);
                    lean_ctor_set(v___x_1025_, 3, v_r_1020_);
                    lean_ctor_set(v___x_1025_, 2, v_v_988_);
                    lean_ctor_set(v___x_1025_, 1, v_k_987_);
                    lean_ctor_set(v___x_1025_, 0, v___x_1033_);
                    v___x_1035_ = v___x_1025_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
                    lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_987_);
                    lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_v_988_);
                    lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_r_1020_);
                    lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_r_990_);
                    v___x_1035_ = v_reuseFailAlloc_1039_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1014_ == 0 {
                    lean_ctor_set(v___x_1013_, 4, v___x_1035_);
                    lean_ctor_set(v___x_1013_, 3, v___y_1030_);
                    lean_ctor_set(v___x_1013_, 2, v_v_1018_);
                    lean_ctor_set(v___x_1013_, 1, v_k_1017_);
                    lean_ctor_set(v___x_1013_, 0, v___x_1028_);
                    v___x_1037_ = v___x_1013_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1028_);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_k_1017_);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_v_1018_);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 3, v___y_1030_);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 4, v___x_1035_);
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
                lean_dec(v___y_1042_);
                lean_dec(v___x_1040_);
                if v_isShared_993_ == 0 {
                    lean_ctor_set(v___x_992_, 4, v_l_1019_);
                    lean_ctor_set(v___x_992_, 3, v_l_1002_);
                    lean_ctor_set(v___x_992_, 2, v_v_1001_);
                    lean_ctor_set(v___x_992_, 1, v_k_1000_);
                    lean_ctor_set(v___x_992_, 0, v___x_1043_);
                    v___x_1045_ = v___x_992_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1043_);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_1000_);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_1001_);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_l_1002_);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_l_1019_);
                    v___x_1045_ = v_reuseFailAlloc_1049_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1046_ = lean_nat_add(v___x_997_, v_size_998_);
                if lean_obj_tag(v_r_1020_) == 0 {
                    v_size_1047_ = lean_ctor_get(v_r_1020_, 0);
                    lean_inc(v_size_1047_);
                    v___y_1030_ = v___x_1045_;
                    v___y_1031_ = v___x_1046_;
                    v___y_1032_ = v_size_1047_;
                    state = 5;
                    continue;
                } else {
                    v___x_1048_ = lean_unsigned_to_nat(0);
                    v___y_1030_ = v___x_1045_;
                    v___y_1031_ = v___x_1046_;
                    v___y_1032_ = v___x_1048_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1070_ = (!lean_is_exclusive(v_r_990_)) as u8;
                if v_isSharedCheck_1070_ == 0 {
                    v_unused_1071_ = lean_ctor_get(v_r_990_, 4);
                    lean_dec(v_unused_1071_);
                    v_unused_1072_ = lean_ctor_get(v_r_990_, 3);
                    lean_dec(v_unused_1072_);
                    v_unused_1073_ = lean_ctor_get(v_r_990_, 2);
                    lean_dec(v_unused_1073_);
                    v_unused_1074_ = lean_ctor_get(v_r_990_, 1);
                    lean_dec(v_unused_1074_);
                    v_unused_1075_ = lean_ctor_get(v_r_990_, 0);
                    lean_dec(v_unused_1075_);
                    v___x_1065_ = v_r_990_;
                    v_isShared_1066_ = v_isSharedCheck_1070_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_990_);
                    v___x_1065_ = lean_box(0);
                    v_isShared_1066_ = v_isSharedCheck_1070_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1066_ == 0 {
                    lean_ctor_set(v___x_1065_, 4, v___x_1063_);
                    lean_ctor_set(v___x_1065_, 3, v_l_1002_);
                    lean_ctor_set(v___x_1065_, 2, v_v_1001_);
                    lean_ctor_set(v___x_1065_, 1, v_k_1000_);
                    lean_ctor_set(v___x_1065_, 0, v___x_1059_);
                    v___x_1068_ = v___x_1065_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1059_);
                    lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_k_1000_);
                    lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_v_1001_);
                    lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_l_1002_);
                    lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___x_1063_);
                    v___x_1068_ = v_reuseFailAlloc_1069_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1068_;
            }
            13 => {
                v___x_1090_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_1084_);
                if v_isShared_1089_ == 0 {
                    lean_ctor_set(v___x_1088_, 3, v_r_1084_);
                    lean_ctor_set(v___x_1088_, 2, v_v_988_);
                    lean_ctor_set(v___x_1088_, 1, v_k_987_);
                    lean_ctor_set(v___x_1088_, 0, v___x_997_);
                    v___x_1092_ = v___x_1088_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_997_);
                    lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_k_987_);
                    lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_v_988_);
                    lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_r_1084_);
                    lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_r_1084_);
                    v___x_1092_ = v_reuseFailAlloc_1096_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_993_ == 0 {
                    lean_ctor_set(v___x_992_, 4, v___x_1092_);
                    lean_ctor_set(v___x_992_, 3, v_l_1083_);
                    lean_ctor_set(v___x_992_, 2, v_v_1086_);
                    lean_ctor_set(v___x_992_, 1, v_k_1085_);
                    lean_ctor_set(v___x_992_, 0, v___x_1090_);
                    v___x_1094_ = v___x_992_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1090_);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_1085_);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_1086_);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_l_1083_);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 4, v___x_1092_);
                    v___x_1094_ = v_reuseFailAlloc_1095_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1094_;
            }
            16 => {
                v_k_1106_ = lean_ctor_get(v_r_1100_, 1);
                v_v_1107_ = lean_ctor_get(v_r_1100_, 2);
                v_isSharedCheck_1121_ = (!lean_is_exclusive(v_r_1100_)) as u8;
                if v_isSharedCheck_1121_ == 0 {
                    v_unused_1122_ = lean_ctor_get(v_r_1100_, 4);
                    lean_dec(v_unused_1122_);
                    v_unused_1123_ = lean_ctor_get(v_r_1100_, 3);
                    lean_dec(v_unused_1123_);
                    v_unused_1124_ = lean_ctor_get(v_r_1100_, 0);
                    lean_dec(v_unused_1124_);
                    v___x_1109_ = v_r_1100_;
                    v_isShared_1110_ = v_isSharedCheck_1121_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_1107_);
                    lean_inc(v_k_1106_);
                    lean_dec(v_r_1100_);
                    v___x_1109_ = lean_box(0);
                    v_isShared_1110_ = v_isSharedCheck_1121_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1111_ = lean_unsigned_to_nat(3);
                if v_isShared_1110_ == 0 {
                    lean_ctor_set(v___x_1109_, 4, v_l_1083_);
                    lean_ctor_set(v___x_1109_, 3, v_l_1083_);
                    lean_ctor_set(v___x_1109_, 2, v_v_1102_);
                    lean_ctor_set(v___x_1109_, 1, v_k_1101_);
                    lean_ctor_set(v___x_1109_, 0, v___x_997_);
                    v___x_1113_ = v___x_1109_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_997_);
                    lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_k_1101_);
                    lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_v_1102_);
                    lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_l_1083_);
                    lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_l_1083_);
                    v___x_1113_ = v_reuseFailAlloc_1120_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1105_ == 0 {
                    lean_ctor_set(v___x_1104_, 4, v_l_1083_);
                    lean_ctor_set(v___x_1104_, 2, v_v_988_);
                    lean_ctor_set(v___x_1104_, 1, v_k_987_);
                    lean_ctor_set(v___x_1104_, 0, v___x_997_);
                    v___x_1115_ = v___x_1104_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_997_);
                    lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_k_987_);
                    lean_ctor_set(v_reuseFailAlloc_1119_, 2, v_v_988_);
                    lean_ctor_set(v_reuseFailAlloc_1119_, 3, v_l_1083_);
                    lean_ctor_set(v_reuseFailAlloc_1119_, 4, v_l_1083_);
                    v___x_1115_ = v_reuseFailAlloc_1119_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_993_ == 0 {
                    lean_ctor_set(v___x_992_, 4, v___x_1115_);
                    lean_ctor_set(v___x_992_, 3, v___x_1113_);
                    lean_ctor_set(v___x_992_, 2, v_v_1107_);
                    lean_ctor_set(v___x_992_, 1, v_k_1106_);
                    lean_ctor_set(v___x_992_, 0, v___x_1111_);
                    v___x_1117_ = v___x_992_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1111_);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_k_1106_);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_v_1107_);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 3, v___x_1113_);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 4, v___x_1115_);
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
                v_size_1155_ = lean_ctor_get(v_l_1142_, 0);
                v_k_1156_ = lean_ctor_get(v_l_1142_, 1);
                v_v_1157_ = lean_ctor_get(v_l_1142_, 2);
                v_l_1158_ = lean_ctor_get(v_l_1142_, 3);
                v_r_1159_ = lean_ctor_get(v_l_1142_, 4);
                v_size_1160_ = lean_ctor_get(v_r_1143_, 0);
                v___x_1161_ = lean_unsigned_to_nat(2);
                v___x_1162_ = lean_nat_mul(v___x_1161_, v_size_1160_);
                v___x_1163_ = lean_nat_dec_lt(v_size_1155_, v___x_1162_);
                lean_dec(v___x_1162_);
                if v___x_1163_ == 0 {
                    lean_inc(v_r_1159_);
                    lean_inc(v_l_1158_);
                    lean_inc(v_v_1157_);
                    lean_inc(v_k_1156_);
                    v_isSharedCheck_1191_ = (!lean_is_exclusive(v_l_1142_)) as u8;
                    if v_isSharedCheck_1191_ == 0 {
                        v_unused_1192_ = lean_ctor_get(v_l_1142_, 4);
                        lean_dec(v_unused_1192_);
                        v_unused_1193_ = lean_ctor_get(v_l_1142_, 3);
                        lean_dec(v_unused_1193_);
                        v_unused_1194_ = lean_ctor_get(v_l_1142_, 2);
                        lean_dec(v_unused_1194_);
                        v_unused_1195_ = lean_ctor_get(v_l_1142_, 1);
                        lean_dec(v_unused_1195_);
                        v_unused_1196_ = lean_ctor_get(v_l_1142_, 0);
                        lean_dec(v_unused_1196_);
                        v___x_1165_ = v_l_1142_;
                        v_isShared_1166_ = v_isSharedCheck_1191_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_1142_);
                        v___x_1165_ = lean_box(0);
                        v_isShared_1166_ = v_isSharedCheck_1191_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_992_);
                    v___x_1197_ = lean_nat_add(v___x_1137_, v_size_1138_);
                    v___x_1198_ = lean_nat_add(v___x_1197_, v_size_1139_);
                    lean_dec(v_size_1139_);
                    v___x_1199_ = lean_nat_add(v___x_1197_, v_size_1155_);
                    lean_dec(v___x_1197_);
                    lean_inc_ref(v_l_989_);
                    if v_isShared_1154_ == 0 {
                        lean_ctor_set(v___x_1153_, 4, v_l_1142_);
                        lean_ctor_set(v___x_1153_, 3, v_l_989_);
                        lean_ctor_set(v___x_1153_, 2, v_v_988_);
                        lean_ctor_set(v___x_1153_, 1, v_k_987_);
                        lean_ctor_set(v___x_1153_, 0, v___x_1199_);
                        v___x_1201_ = v___x_1153_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1199_);
                        lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_987_);
                        lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_988_);
                        lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_l_989_);
                        lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_l_1142_);
                        v___x_1201_ = v_reuseFailAlloc_1214_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1167_ = lean_nat_add(v___x_1137_, v_size_1138_);
                v___x_1168_ = lean_nat_add(v___x_1167_, v_size_1139_);
                lean_dec(v_size_1139_);
                if lean_obj_tag(v_l_1158_) == 0 {
                    v_size_1189_ = lean_ctor_get(v_l_1158_, 0);
                    lean_inc(v_size_1189_);
                    v___y_1181_ = v_size_1189_;
                    state = 29;
                    continue;
                } else {
                    v___x_1190_ = lean_unsigned_to_nat(0);
                    v___y_1181_ = v___x_1190_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1173_ = lean_nat_add(v___y_1170_, v___y_1172_);
                lean_dec(v___y_1172_);
                lean_dec(v___y_1170_);
                if v_isShared_1166_ == 0 {
                    lean_ctor_set(v___x_1165_, 4, v_r_1143_);
                    lean_ctor_set(v___x_1165_, 3, v_r_1159_);
                    lean_ctor_set(v___x_1165_, 2, v_v_1141_);
                    lean_ctor_set(v___x_1165_, 1, v_k_1140_);
                    lean_ctor_set(v___x_1165_, 0, v___x_1173_);
                    v___x_1175_ = v___x_1165_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1173_);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_k_1140_);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_v_1141_);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_r_1159_);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_r_1143_);
                    v___x_1175_ = v_reuseFailAlloc_1179_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1154_ == 0 {
                    lean_ctor_set(v___x_1153_, 4, v___x_1175_);
                    lean_ctor_set(v___x_1153_, 3, v___y_1171_);
                    lean_ctor_set(v___x_1153_, 2, v_v_1157_);
                    lean_ctor_set(v___x_1153_, 1, v_k_1156_);
                    lean_ctor_set(v___x_1153_, 0, v___x_1168_);
                    v___x_1177_ = v___x_1153_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1168_);
                    lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_k_1156_);
                    lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_v_1157_);
                    lean_ctor_set(v_reuseFailAlloc_1178_, 3, v___y_1171_);
                    lean_ctor_set(v_reuseFailAlloc_1178_, 4, v___x_1175_);
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
                lean_dec(v___y_1181_);
                lean_dec(v___x_1167_);
                if v_isShared_993_ == 0 {
                    lean_ctor_set(v___x_992_, 4, v_l_1158_);
                    lean_ctor_set(v___x_992_, 0, v___x_1182_);
                    v___x_1184_ = v___x_992_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1182_);
                    lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_k_987_);
                    lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_v_988_);
                    lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_l_989_);
                    lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_l_1158_);
                    v___x_1184_ = v_reuseFailAlloc_1188_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1185_ = lean_nat_add(v___x_1137_, v_size_1160_);
                if lean_obj_tag(v_r_1159_) == 0 {
                    v_size_1186_ = lean_ctor_get(v_r_1159_, 0);
                    lean_inc(v_size_1186_);
                    v___y_1170_ = v___x_1185_;
                    v___y_1171_ = v___x_1184_;
                    v___y_1172_ = v_size_1186_;
                    state = 26;
                    continue;
                } else {
                    v___x_1187_ = lean_unsigned_to_nat(0);
                    v___y_1170_ = v___x_1185_;
                    v___y_1171_ = v___x_1184_;
                    v___y_1172_ = v___x_1187_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1208_ = (!lean_is_exclusive(v_l_989_)) as u8;
                if v_isSharedCheck_1208_ == 0 {
                    v_unused_1209_ = lean_ctor_get(v_l_989_, 4);
                    lean_dec(v_unused_1209_);
                    v_unused_1210_ = lean_ctor_get(v_l_989_, 3);
                    lean_dec(v_unused_1210_);
                    v_unused_1211_ = lean_ctor_get(v_l_989_, 2);
                    lean_dec(v_unused_1211_);
                    v_unused_1212_ = lean_ctor_get(v_l_989_, 1);
                    lean_dec(v_unused_1212_);
                    v_unused_1213_ = lean_ctor_get(v_l_989_, 0);
                    lean_dec(v_unused_1213_);
                    v___x_1203_ = v_l_989_;
                    v_isShared_1204_ = v_isSharedCheck_1208_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_989_);
                    v___x_1203_ = lean_box(0);
                    v_isShared_1204_ = v_isSharedCheck_1208_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1204_ == 0 {
                    lean_ctor_set(v___x_1203_, 4, v_r_1143_);
                    lean_ctor_set(v___x_1203_, 3, v___x_1201_);
                    lean_ctor_set(v___x_1203_, 2, v_v_1141_);
                    lean_ctor_set(v___x_1203_, 1, v_k_1140_);
                    lean_ctor_set(v___x_1203_, 0, v___x_1198_);
                    v___x_1206_ = v___x_1203_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1198_);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_k_1140_);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_v_1141_);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 3, v___x_1201_);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_r_1143_);
                    v___x_1206_ = v_reuseFailAlloc_1207_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1206_;
            }
            34 => {
                v_k_1228_ = lean_ctor_get(v_l_1221_, 1);
                v_v_1229_ = lean_ctor_get(v_l_1221_, 2);
                v_isSharedCheck_1243_ = (!lean_is_exclusive(v_l_1221_)) as u8;
                if v_isSharedCheck_1243_ == 0 {
                    v_unused_1244_ = lean_ctor_get(v_l_1221_, 4);
                    lean_dec(v_unused_1244_);
                    v_unused_1245_ = lean_ctor_get(v_l_1221_, 3);
                    lean_dec(v_unused_1245_);
                    v_unused_1246_ = lean_ctor_get(v_l_1221_, 0);
                    lean_dec(v_unused_1246_);
                    v___x_1231_ = v_l_1221_;
                    v_isShared_1232_ = v_isSharedCheck_1243_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_1229_);
                    lean_inc(v_k_1228_);
                    lean_dec(v_l_1221_);
                    v___x_1231_ = lean_box(0);
                    v_isShared_1232_ = v_isSharedCheck_1243_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1233_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_1222_, 2);
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 4, v_r_1222_);
                    lean_ctor_set(v___x_1231_, 3, v_r_1222_);
                    lean_ctor_set(v___x_1231_, 2, v_v_988_);
                    lean_ctor_set(v___x_1231_, 1, v_k_987_);
                    lean_ctor_set(v___x_1231_, 0, v___x_1137_);
                    v___x_1235_ = v___x_1231_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1137_);
                    lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_k_987_);
                    lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_v_988_);
                    lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_r_1222_);
                    lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_r_1222_);
                    v___x_1235_ = v_reuseFailAlloc_1242_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_1222_);
                if v_isShared_1227_ == 0 {
                    lean_ctor_set(v___x_1226_, 3, v_r_1222_);
                    lean_ctor_set(v___x_1226_, 0, v___x_1137_);
                    v___x_1237_ = v___x_1226_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1137_);
                    lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_k_1223_);
                    lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_v_1224_);
                    lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_r_1222_);
                    lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_r_1222_);
                    v___x_1237_ = v_reuseFailAlloc_1241_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_993_ == 0 {
                    lean_ctor_set(v___x_992_, 4, v___x_1237_);
                    lean_ctor_set(v___x_992_, 3, v___x_1235_);
                    lean_ctor_set(v___x_992_, 2, v_v_1229_);
                    lean_ctor_set(v___x_992_, 1, v_k_1228_);
                    lean_ctor_set(v___x_992_, 0, v___x_1233_);
                    v___x_1239_ = v___x_992_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1233_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1228_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1229_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 3, v___x_1235_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 4, v___x_1237_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1239_;
            }
            39 => {
                v___x_1256_ = lean_unsigned_to_nat(3);
                if v_isShared_1255_ == 0 {
                    lean_ctor_set(v___x_1254_, 4, v_l_1221_);
                    lean_ctor_set(v___x_1254_, 2, v_v_988_);
                    lean_ctor_set(v___x_1254_, 1, v_k_987_);
                    lean_ctor_set(v___x_1254_, 0, v___x_1137_);
                    v___x_1258_ = v___x_1254_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1137_);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_k_987_);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_v_988_);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 3, v_l_1221_);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 4, v_l_1221_);
                    v___x_1258_ = v_reuseFailAlloc_1262_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_993_ == 0 {
                    lean_ctor_set(v___x_992_, 4, v_r_1250_);
                    lean_ctor_set(v___x_992_, 3, v___x_1258_);
                    lean_ctor_set(v___x_992_, 2, v_v_1252_);
                    lean_ctor_set(v___x_992_, 1, v_k_1251_);
                    lean_ctor_set(v___x_992_, 0, v___x_1256_);
                    v___x_1260_ = v___x_992_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1256_);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1251_);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1252_);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 3, v___x_1258_);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_r_1250_);
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
    mut v_cmp_1274_: *mut LeanObject,
    mut v_k_1275_: *mut LeanObject,
    mut v_t_1276_: *mut LeanObject,
) -> u8 {
    let mut v_k_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u8 = 0;
    let mut v___x_1283_: u8 = 0;
    let mut v___x_1285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1276_) == 0 {
                    v_k_1277_ = lean_ctor_get(v_t_1276_, 1);
                    lean_inc(v_k_1277_);
                    v_l_1278_ = lean_ctor_get(v_t_1276_, 3);
                    lean_inc(v_l_1278_);
                    v_r_1279_ = lean_ctor_get(v_t_1276_, 4);
                    lean_inc(v_r_1279_);
                    lean_dec_ref_known(v_t_1276_, 5);
                    lean_inc_ref(v_cmp_1274_);
                    lean_inc(v_k_1275_);
                    v___x_1280_ = lean_apply_2(v_cmp_1274_, v_k_1275_, v_k_1277_);
                    v___x_1281_ = (lean_unbox(v___x_1280_) as u8);
                    match v___x_1281_ {
                        0 => {
                            lean_dec(v_r_1279_);
                            v_t_1276_ = v_l_1278_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_1279_);
                            lean_dec(v_l_1278_);
                            lean_dec(v_k_1275_);
                            lean_dec_ref(v_cmp_1274_);
                            v___x_1283_ = 1;
                            return v___x_1283_;
                        }
                        _ => {
                            lean_dec(v_l_1278_);
                            v_t_1276_ = v_r_1279_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_1275_);
                    lean_dec_ref(v_cmp_1274_);
                    v___x_1285_ = 0;
                    return v___x_1285_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg___boxed(
    mut v_cmp_1286_: *mut LeanObject,
    mut v_k_1287_: *mut LeanObject,
    mut v_t_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1289_: u8 = 0;
    let mut v_r_1290_: *mut LeanObject = core::ptr::null_mut();
    v_res_1289_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(
            v_cmp_1286_,
            v_k_1287_,
            v_t_1288_,
        );
    v_r_1290_ = lean_box((v_res_1289_) as usize);
    return v_r_1290_;
}
pub unsafe fn l_Lake_RBArray_insert___redArg(
    mut v_cmp_1291_: *mut LeanObject,
    mut v_self_1292_: *mut LeanObject,
    mut v_a_1293_: *mut LeanObject,
    mut v_b_1294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toTreeMap_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toArray_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_unused_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toTreeMap_1295_ = lean_ctor_get(v_self_1292_, 0);
                v_toArray_1296_ = lean_ctor_get(v_self_1292_, 1);
                lean_inc(v_toTreeMap_1295_);
                lean_inc(v_a_1293_);
                lean_inc_ref(v_cmp_1291_);
                v___x_1297_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_1291_, v_a_1293_, v_toTreeMap_1295_);
                if v___x_1297_ == 0 {
                    lean_inc_ref(v_toArray_1296_);
                    lean_inc(v_toTreeMap_1295_);
                    v_isSharedCheck_1306_ = (!lean_is_exclusive(v_self_1292_)) as u8;
                    if v_isSharedCheck_1306_ == 0 {
                        v_unused_1307_ = lean_ctor_get(v_self_1292_, 1);
                        lean_dec(v_unused_1307_);
                        v_unused_1308_ = lean_ctor_get(v_self_1292_, 0);
                        lean_dec(v_unused_1308_);
                        v___x_1299_ = v_self_1292_;
                        v_isShared_1300_ = v_isSharedCheck_1306_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_self_1292_);
                        v___x_1299_ = lean_box(0);
                        v_isShared_1300_ = v_isSharedCheck_1306_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1294_);
                    lean_dec(v_a_1293_);
                    lean_dec_ref(v_cmp_1291_);
                    return v_self_1292_;
                }
            }
            1 => {
                lean_inc(v_b_1294_);
                v___x_1301_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_1291_, v_a_1293_, v_b_1294_, v_toTreeMap_1295_);
                v___x_1302_ = lean_array_push(v_toArray_1296_, v_b_1294_);
                if v_isShared_1300_ == 0 {
                    lean_ctor_set(v___x_1299_, 1, v___x_1302_);
                    lean_ctor_set(v___x_1299_, 0, v___x_1301_);
                    v___x_1304_ = v___x_1299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1301_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
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
    mut v_00_u03b1_1309_: *mut LeanObject,
    mut v_00_u03b2_1310_: *mut LeanObject,
    mut v_cmp_1311_: *mut LeanObject,
    mut v_self_1312_: *mut LeanObject,
    mut v_a_1313_: *mut LeanObject,
    mut v_b_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lake_RBArray_insert___redArg(v_cmp_1311_, v_self_1312_, v_a_1313_, v_b_1314_);
    return v___x_1315_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(
    mut v_00_u03b1_1316_: *mut LeanObject,
    mut v_cmp_1317_: *mut LeanObject,
    mut v_00_u03b2_1318_: *mut LeanObject,
    mut v_k_1319_: *mut LeanObject,
    mut v_t_1320_: *mut LeanObject,
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
    mut v_00_u03b1_1322_: *mut LeanObject,
    mut v_cmp_1323_: *mut LeanObject,
    mut v_00_u03b2_1324_: *mut LeanObject,
    mut v_k_1325_: *mut LeanObject,
    mut v_t_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1327_: u8 = 0;
    let mut v_r_1328_: *mut LeanObject = core::ptr::null_mut();
    v_res_1327_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(
        v_00_u03b1_1322_,
        v_cmp_1323_,
        v_00_u03b2_1324_,
        v_k_1325_,
        v_t_1326_,
    );
    v_r_1328_ = lean_box((v_res_1327_) as usize);
    return v_r_1328_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1(
    mut v_00_u03b1_1329_: *mut LeanObject,
    mut v_cmp_1330_: *mut LeanObject,
    mut v_00_u03b2_1331_: *mut LeanObject,
    mut v_k_1332_: *mut LeanObject,
    mut v_v_1333_: *mut LeanObject,
    mut v_t_1334_: *mut LeanObject,
    mut v_hl_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    v___x_1336_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(
        v_cmp_1330_,
        v_k_1332_,
        v_v_1333_,
        v_t_1334_,
    );
    return v___x_1336_;
}
pub unsafe fn l_Lake_RBArray_all___redArg___lam__0(
    mut v_f_1337_: *mut LeanObject,
    mut v___x_1338_: u8,
    mut v_v_1339_: *mut LeanObject,
) -> u8 {
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    v___x_1340_ = lean_apply_1(v_f_1337_, v_v_1339_);
    v___x_1341_ = (lean_unbox(v___x_1340_) as u8);
    if v___x_1341_ == 0 {
        return v___x_1338_;
    } else {
        let mut v___x_1342_: u8 = 0;
        v___x_1342_ = 0;
        return v___x_1342_;
    }
}
pub unsafe fn l_Lake_RBArray_all___redArg___lam__0___boxed(
    mut v_f_1343_: *mut LeanObject,
    mut v___x_1344_: *mut LeanObject,
    mut v_v_1345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_79__boxed_1346_: u8 = 0;
    let mut v_res_1347_: u8 = 0;
    let mut v_r_1348_: *mut LeanObject = core::ptr::null_mut();
    v___x_79__boxed_1346_ = (lean_unbox(v___x_1344_) as u8);
    v_res_1347_ = l_Lake_RBArray_all___redArg___lam__0(v_f_1343_, v___x_79__boxed_1346_, v_v_1345_);
    v_r_1348_ = lean_box((v_res_1347_) as usize);
    return v_r_1348_;
}
pub unsafe fn l_Lake_RBArray_all___redArg(
    mut v_f_1368_: *mut LeanObject,
    mut v_self_1369_: *mut LeanObject,
) -> u8 {
    let mut v_toArray_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    v_toArray_1370_ = lean_ctor_get(v_self_1369_, 1);
    lean_inc_ref(v_toArray_1370_);
    lean_dec_ref(v_self_1369_);
    v___x_1371_ = lean_unsigned_to_nat(0);
    v___x_1372_ = lean_array_get_size(v_toArray_1370_);
    v___x_1373_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1374_ = lean_nat_dec_lt(v___x_1371_, v___x_1372_);
    if v___x_1374_ == 0 {
        let mut v___x_1375_: u8 = 0;
        lean_dec_ref(v_toArray_1370_);
        lean_dec_ref(v_f_1368_);
        v___x_1375_ = 1;
        return v___x_1375_;
    } else {
        if v___x_1374_ == 0 {
            lean_dec_ref(v_toArray_1370_);
            lean_dec_ref(v_f_1368_);
            return v___x_1374_;
        } else {
            let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1377_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1378_: usize = 0;
            let mut v___x_1379_: usize = 0;
            let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1381_: u8 = 0;
            v___x_1376_ = lean_box((v___x_1374_) as usize);
            v___f_1377_ = lean_alloc_closure(
                l_Lake_RBArray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_1377_, 0, v_f_1368_);
            lean_closure_set(v___f_1377_, 1, v___x_1376_);
            v___x_1378_ = 0usize;
            v___x_1379_ = lean_usize_of_nat(v___x_1372_);
            v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_1373_,
                v___f_1377_,
                v_toArray_1370_,
                v___x_1378_,
                v___x_1379_,
            );
            v___x_1381_ = (lean_unbox(v___x_1380_) as u8);
            lean_dec(v___x_1380_);
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
    mut v_f_1383_: *mut LeanObject,
    mut v_self_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1385_: u8 = 0;
    let mut v_r_1386_: *mut LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lake_RBArray_all___redArg(v_f_1383_, v_self_1384_);
    v_r_1386_ = lean_box((v_res_1385_) as usize);
    return v_r_1386_;
}
pub unsafe fn l_Lake_RBArray_all(
    mut v_00_u03b2_1387_: *mut LeanObject,
    mut v_00_u03b1_1388_: *mut LeanObject,
    mut v_cmp_1389_: *mut LeanObject,
    mut v_f_1390_: *mut LeanObject,
    mut v_self_1391_: *mut LeanObject,
) -> u8 {
    let mut v_toArray_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    v_toArray_1392_ = lean_ctor_get(v_self_1391_, 1);
    lean_inc_ref(v_toArray_1392_);
    lean_dec_ref(v_self_1391_);
    v___x_1393_ = lean_unsigned_to_nat(0);
    v___x_1394_ = lean_array_get_size(v_toArray_1392_);
    v___x_1395_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1396_ = lean_nat_dec_lt(v___x_1393_, v___x_1394_);
    if v___x_1396_ == 0 {
        let mut v___x_1397_: u8 = 0;
        lean_dec_ref(v_toArray_1392_);
        lean_dec_ref(v_f_1390_);
        v___x_1397_ = 1;
        return v___x_1397_;
    } else {
        if v___x_1396_ == 0 {
            lean_dec_ref(v_toArray_1392_);
            lean_dec_ref(v_f_1390_);
            return v___x_1396_;
        } else {
            let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1399_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1400_: usize = 0;
            let mut v___x_1401_: usize = 0;
            let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1403_: u8 = 0;
            v___x_1398_ = lean_box((v___x_1396_) as usize);
            v___f_1399_ = lean_alloc_closure(
                l_Lake_RBArray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_1399_, 0, v_f_1390_);
            lean_closure_set(v___f_1399_, 1, v___x_1398_);
            v___x_1400_ = 0usize;
            v___x_1401_ = lean_usize_of_nat(v___x_1394_);
            v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_1395_,
                v___f_1399_,
                v_toArray_1392_,
                v___x_1400_,
                v___x_1401_,
            );
            v___x_1403_ = (lean_unbox(v___x_1402_) as u8);
            lean_dec(v___x_1402_);
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
    mut v_00_u03b2_1405_: *mut LeanObject,
    mut v_00_u03b1_1406_: *mut LeanObject,
    mut v_cmp_1407_: *mut LeanObject,
    mut v_f_1408_: *mut LeanObject,
    mut v_self_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1410_: u8 = 0;
    let mut v_r_1411_: *mut LeanObject = core::ptr::null_mut();
    v_res_1410_ = l_Lake_RBArray_all(
        v_00_u03b2_1405_,
        v_00_u03b1_1406_,
        v_cmp_1407_,
        v_f_1408_,
        v_self_1409_,
    );
    lean_dec_ref(v_cmp_1407_);
    v_r_1411_ = lean_box((v_res_1410_) as usize);
    return v_r_1411_;
}
pub unsafe fn l_Lake_RBArray_any___redArg___lam__0(
    mut v_f_1412_: *mut LeanObject,
    mut v_x_1413_: *mut LeanObject,
) -> u8 {
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    v___x_1414_ = lean_apply_1(v_f_1412_, v_x_1413_);
    v___x_1415_ = (lean_unbox(v___x_1414_) as u8);
    return v___x_1415_;
}
pub unsafe fn l_Lake_RBArray_any___redArg___lam__0___boxed(
    mut v_f_1416_: *mut LeanObject,
    mut v_x_1417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1418_: u8 = 0;
    let mut v_r_1419_: *mut LeanObject = core::ptr::null_mut();
    v_res_1418_ = l_Lake_RBArray_any___redArg___lam__0(v_f_1416_, v_x_1417_);
    v_r_1419_ = lean_box((v_res_1418_) as usize);
    return v_r_1419_;
}
pub unsafe fn l_Lake_RBArray_any___redArg(
    mut v_f_1420_: *mut LeanObject,
    mut v_self_1421_: *mut LeanObject,
) -> u8 {
    let mut v_toArray_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    v_toArray_1422_ = lean_ctor_get(v_self_1421_, 1);
    lean_inc_ref(v_toArray_1422_);
    lean_dec_ref(v_self_1421_);
    v___x_1423_ = lean_unsigned_to_nat(0);
    v___x_1424_ = lean_array_get_size(v_toArray_1422_);
    v___x_1425_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1426_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
    if v___x_1426_ == 0 {
        lean_dec_ref(v_toArray_1422_);
        lean_dec_ref(v_f_1420_);
        return v___x_1426_;
    } else {
        if v___x_1426_ == 0 {
            lean_dec_ref(v_toArray_1422_);
            lean_dec_ref(v_f_1420_);
            return v___x_1426_;
        } else {
            let mut v___f_1427_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1428_: usize = 0;
            let mut v___x_1429_: usize = 0;
            let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1431_: u8 = 0;
            v___f_1427_ = lean_alloc_closure(
                l_Lake_RBArray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_1427_, 0, v_f_1420_);
            v___x_1428_ = 0usize;
            v___x_1429_ = lean_usize_of_nat(v___x_1424_);
            v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_1425_,
                v___f_1427_,
                v_toArray_1422_,
                v___x_1428_,
                v___x_1429_,
            );
            v___x_1431_ = (lean_unbox(v___x_1430_) as u8);
            lean_dec(v___x_1430_);
            return v___x_1431_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_any___redArg___boxed(
    mut v_f_1432_: *mut LeanObject,
    mut v_self_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1434_: u8 = 0;
    let mut v_r_1435_: *mut LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lake_RBArray_any___redArg(v_f_1432_, v_self_1433_);
    v_r_1435_ = lean_box((v_res_1434_) as usize);
    return v_r_1435_;
}
pub unsafe fn l_Lake_RBArray_any(
    mut v_00_u03b2_1436_: *mut LeanObject,
    mut v_00_u03b1_1437_: *mut LeanObject,
    mut v_cmp_1438_: *mut LeanObject,
    mut v_f_1439_: *mut LeanObject,
    mut v_self_1440_: *mut LeanObject,
) -> u8 {
    let mut v_toArray_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    v_toArray_1441_ = lean_ctor_get(v_self_1440_, 1);
    lean_inc_ref(v_toArray_1441_);
    lean_dec_ref(v_self_1440_);
    v___x_1442_ = lean_unsigned_to_nat(0);
    v___x_1443_ = lean_array_get_size(v_toArray_1441_);
    v___x_1444_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1445_ = lean_nat_dec_lt(v___x_1442_, v___x_1443_);
    if v___x_1445_ == 0 {
        lean_dec_ref(v_toArray_1441_);
        lean_dec_ref(v_f_1439_);
        return v___x_1445_;
    } else {
        if v___x_1445_ == 0 {
            lean_dec_ref(v_toArray_1441_);
            lean_dec_ref(v_f_1439_);
            return v___x_1445_;
        } else {
            let mut v___f_1446_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1447_: usize = 0;
            let mut v___x_1448_: usize = 0;
            let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1450_: u8 = 0;
            v___f_1446_ = lean_alloc_closure(
                l_Lake_RBArray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_1446_, 0, v_f_1439_);
            v___x_1447_ = 0usize;
            v___x_1448_ = lean_usize_of_nat(v___x_1443_);
            v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_1444_,
                v___f_1446_,
                v_toArray_1441_,
                v___x_1447_,
                v___x_1448_,
            );
            v___x_1450_ = (lean_unbox(v___x_1449_) as u8);
            lean_dec(v___x_1449_);
            return v___x_1450_;
        }
    }
}
pub unsafe fn l_Lake_RBArray_any___boxed(
    mut v_00_u03b2_1451_: *mut LeanObject,
    mut v_00_u03b1_1452_: *mut LeanObject,
    mut v_cmp_1453_: *mut LeanObject,
    mut v_f_1454_: *mut LeanObject,
    mut v_self_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: u8 = 0;
    let mut v_r_1457_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ = l_Lake_RBArray_any(
        v_00_u03b2_1451_,
        v_00_u03b1_1452_,
        v_cmp_1453_,
        v_f_1454_,
        v_self_1455_,
    );
    lean_dec_ref(v_cmp_1453_);
    v_r_1457_ = lean_box((v_res_1456_) as usize);
    return v_r_1457_;
}
pub unsafe fn l_Lake_RBArray_foldl___redArg___lam__0(
    mut v_f_1458_: *mut LeanObject,
    mut v_x1_1459_: *mut LeanObject,
    mut v_x2_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    v___x_1461_ = lean_apply_2(v_f_1458_, v_x1_1459_, v_x2_1460_);
    return v___x_1461_;
}
pub unsafe fn l_Lake_RBArray_foldl___redArg(
    mut v_f_1462_: *mut LeanObject,
    mut v_init_1463_: *mut LeanObject,
    mut v_self_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    v_toArray_1465_ = lean_ctor_get(v_self_1464_, 1);
    lean_inc_ref(v_toArray_1465_);
    lean_dec_ref(v_self_1464_);
    v___x_1466_ = lean_unsigned_to_nat(0);
    v___x_1467_ = lean_array_get_size(v_toArray_1465_);
    v___x_1468_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1469_ = lean_nat_dec_lt(v___x_1466_, v___x_1467_);
    if v___x_1469_ == 0 {
        lean_dec_ref(v_toArray_1465_);
        lean_dec(v_f_1462_);
        return v_init_1463_;
    } else {
        let mut v___f_1470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1471_: u8 = 0;
        v___f_1470_ = lean_alloc_closure(
            l_Lake_RBArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1470_, 0, v_f_1462_);
        v___x_1471_ = lean_nat_dec_le(v___x_1467_, v___x_1467_);
        if v___x_1471_ == 0 {
            if v___x_1469_ == 0 {
                lean_dec_ref(v___f_1470_);
                lean_dec_ref(v_toArray_1465_);
                return v_init_1463_;
            } else {
                let mut v___x_1472_: usize = 0;
                let mut v___x_1473_: usize = 0;
                let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
                v___x_1472_ = 0usize;
                v___x_1473_ = lean_usize_of_nat(v___x_1467_);
                v___x_1474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
            v___x_1475_ = 0usize;
            v___x_1476_ = lean_usize_of_nat(v___x_1467_);
            v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03c3_1478_: *mut LeanObject,
    mut v_00_u03b2_1479_: *mut LeanObject,
    mut v_00_u03b1_1480_: *mut LeanObject,
    mut v_cmp_1481_: *mut LeanObject,
    mut v_f_1482_: *mut LeanObject,
    mut v_init_1483_: *mut LeanObject,
    mut v_self_1484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: u8 = 0;
    v_toArray_1485_ = lean_ctor_get(v_self_1484_, 1);
    lean_inc_ref(v_toArray_1485_);
    lean_dec_ref(v_self_1484_);
    v___x_1486_ = lean_unsigned_to_nat(0);
    v___x_1487_ = lean_array_get_size(v_toArray_1485_);
    v___x_1488_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1489_ = lean_nat_dec_lt(v___x_1486_, v___x_1487_);
    if v___x_1489_ == 0 {
        lean_dec_ref(v_toArray_1485_);
        lean_dec(v_f_1482_);
        return v_init_1483_;
    } else {
        let mut v___f_1490_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1491_: u8 = 0;
        v___f_1490_ = lean_alloc_closure(
            l_Lake_RBArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1490_, 0, v_f_1482_);
        v___x_1491_ = lean_nat_dec_le(v___x_1487_, v___x_1487_);
        if v___x_1491_ == 0 {
            if v___x_1489_ == 0 {
                lean_dec_ref(v___f_1490_);
                lean_dec_ref(v_toArray_1485_);
                return v_init_1483_;
            } else {
                let mut v___x_1492_: usize = 0;
                let mut v___x_1493_: usize = 0;
                let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
                v___x_1492_ = 0usize;
                v___x_1493_ = lean_usize_of_nat(v___x_1487_);
                v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
            v___x_1495_ = 0usize;
            v___x_1496_ = lean_usize_of_nat(v___x_1487_);
            v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03c3_1498_: *mut LeanObject,
    mut v_00_u03b2_1499_: *mut LeanObject,
    mut v_00_u03b1_1500_: *mut LeanObject,
    mut v_cmp_1501_: *mut LeanObject,
    mut v_f_1502_: *mut LeanObject,
    mut v_init_1503_: *mut LeanObject,
    mut v_self_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1505_: *mut LeanObject = core::ptr::null_mut();
    v_res_1505_ = l_Lake_RBArray_foldl(
        v_00_u03c3_1498_,
        v_00_u03b2_1499_,
        v_00_u03b1_1500_,
        v_cmp_1501_,
        v_f_1502_,
        v_init_1503_,
        v_self_1504_,
    );
    lean_dec_ref(v_cmp_1501_);
    return v_res_1505_;
}
pub unsafe fn l_Lake_RBArray_foldlM___redArg(
    mut v_inst_1506_: *mut LeanObject,
    mut v_f_1507_: *mut LeanObject,
    mut v_init_1508_: *mut LeanObject,
    mut v_self_1509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    v_toArray_1510_ = lean_ctor_get(v_self_1509_, 1);
    lean_inc_ref(v_toArray_1510_);
    lean_dec_ref(v_self_1509_);
    v___x_1511_ = lean_unsigned_to_nat(0);
    v___x_1512_ = lean_array_get_size(v_toArray_1510_);
    v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
    if v___x_1513_ == 0 {
        let mut v_toApplicative_1514_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1510_);
        lean_dec(v_f_1507_);
        v_toApplicative_1514_ = lean_ctor_get(v_inst_1506_, 0);
        lean_inc_ref(v_toApplicative_1514_);
        lean_dec_ref(v_inst_1506_);
        v_toPure_1515_ = lean_ctor_get(v_toApplicative_1514_, 1);
        lean_inc(v_toPure_1515_);
        lean_dec_ref(v_toApplicative_1514_);
        v___x_1516_ = lean_apply_2(v_toPure_1515_, lean_box(0), v_init_1508_);
        return v___x_1516_;
    } else {
        let mut v___x_1517_: u8 = 0;
        v___x_1517_ = lean_nat_dec_le(v___x_1512_, v___x_1512_);
        if v___x_1517_ == 0 {
            if v___x_1513_ == 0 {
                let mut v_toApplicative_1518_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_1519_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toArray_1510_);
                lean_dec(v_f_1507_);
                v_toApplicative_1518_ = lean_ctor_get(v_inst_1506_, 0);
                lean_inc_ref(v_toApplicative_1518_);
                lean_dec_ref(v_inst_1506_);
                v_toPure_1519_ = lean_ctor_get(v_toApplicative_1518_, 1);
                lean_inc(v_toPure_1519_);
                lean_dec_ref(v_toApplicative_1518_);
                v___x_1520_ = lean_apply_2(v_toPure_1519_, lean_box(0), v_init_1508_);
                return v___x_1520_;
            } else {
                let mut v___x_1521_: usize = 0;
                let mut v___x_1522_: usize = 0;
                let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
                v___x_1521_ = 0usize;
                v___x_1522_ = lean_usize_of_nat(v___x_1512_);
                v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
            v___x_1524_ = 0usize;
            v___x_1525_ = lean_usize_of_nat(v___x_1512_);
            v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_m_1527_: *mut LeanObject,
    mut v_00_u03c3_1528_: *mut LeanObject,
    mut v_00_u03b2_1529_: *mut LeanObject,
    mut v_00_u03b1_1530_: *mut LeanObject,
    mut v_cmp_1531_: *mut LeanObject,
    mut v_inst_1532_: *mut LeanObject,
    mut v_f_1533_: *mut LeanObject,
    mut v_init_1534_: *mut LeanObject,
    mut v_self_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    v_toArray_1536_ = lean_ctor_get(v_self_1535_, 1);
    lean_inc_ref(v_toArray_1536_);
    lean_dec_ref(v_self_1535_);
    v___x_1537_ = lean_unsigned_to_nat(0);
    v___x_1538_ = lean_array_get_size(v_toArray_1536_);
    v___x_1539_ = lean_nat_dec_lt(v___x_1537_, v___x_1538_);
    if v___x_1539_ == 0 {
        let mut v_toApplicative_1540_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1536_);
        lean_dec(v_f_1533_);
        v_toApplicative_1540_ = lean_ctor_get(v_inst_1532_, 0);
        lean_inc_ref(v_toApplicative_1540_);
        lean_dec_ref(v_inst_1532_);
        v_toPure_1541_ = lean_ctor_get(v_toApplicative_1540_, 1);
        lean_inc(v_toPure_1541_);
        lean_dec_ref(v_toApplicative_1540_);
        v___x_1542_ = lean_apply_2(v_toPure_1541_, lean_box(0), v_init_1534_);
        return v___x_1542_;
    } else {
        let mut v___x_1543_: u8 = 0;
        v___x_1543_ = lean_nat_dec_le(v___x_1538_, v___x_1538_);
        if v___x_1543_ == 0 {
            if v___x_1539_ == 0 {
                let mut v_toApplicative_1544_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_1545_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toArray_1536_);
                lean_dec(v_f_1533_);
                v_toApplicative_1544_ = lean_ctor_get(v_inst_1532_, 0);
                lean_inc_ref(v_toApplicative_1544_);
                lean_dec_ref(v_inst_1532_);
                v_toPure_1545_ = lean_ctor_get(v_toApplicative_1544_, 1);
                lean_inc(v_toPure_1545_);
                lean_dec_ref(v_toApplicative_1544_);
                v___x_1546_ = lean_apply_2(v_toPure_1545_, lean_box(0), v_init_1534_);
                return v___x_1546_;
            } else {
                let mut v___x_1547_: usize = 0;
                let mut v___x_1548_: usize = 0;
                let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
                v___x_1547_ = 0usize;
                v___x_1548_ = lean_usize_of_nat(v___x_1538_);
                v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
            v___x_1550_ = 0usize;
            v___x_1551_ = lean_usize_of_nat(v___x_1538_);
            v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_m_1553_: *mut LeanObject,
    mut v_00_u03c3_1554_: *mut LeanObject,
    mut v_00_u03b2_1555_: *mut LeanObject,
    mut v_00_u03b1_1556_: *mut LeanObject,
    mut v_cmp_1557_: *mut LeanObject,
    mut v_inst_1558_: *mut LeanObject,
    mut v_f_1559_: *mut LeanObject,
    mut v_init_1560_: *mut LeanObject,
    mut v_self_1561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1562_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_cmp_1557_);
    return v_res_1562_;
}
pub unsafe fn l_Lake_RBArray_foldr___redArg(
    mut v_f_1563_: *mut LeanObject,
    mut v_init_1564_: *mut LeanObject,
    mut v_self_1565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    v_toArray_1566_ = lean_ctor_get(v_self_1565_, 1);
    lean_inc_ref(v_toArray_1566_);
    lean_dec_ref(v_self_1565_);
    v___x_1567_ = lean_array_get_size(v_toArray_1566_);
    v___x_1568_ = lean_unsigned_to_nat(0);
    v___x_1569_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1570_ = lean_nat_dec_lt(v___x_1568_, v___x_1567_);
    if v___x_1570_ == 0 {
        lean_dec_ref(v_toArray_1566_);
        lean_dec(v_f_1563_);
        return v_init_1564_;
    } else {
        let mut v___f_1571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: usize = 0;
        let mut v___x_1573_: usize = 0;
        let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
        v___f_1571_ = lean_alloc_closure(
            l_Lake_RBArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1571_, 0, v_f_1563_);
        v___x_1572_ = lean_usize_of_nat(v___x_1567_);
        v___x_1573_ = 0usize;
        v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b2_1575_: *mut LeanObject,
    mut v_00_u03c3_1576_: *mut LeanObject,
    mut v_00_u03b1_1577_: *mut LeanObject,
    mut v_cmp_1578_: *mut LeanObject,
    mut v_f_1579_: *mut LeanObject,
    mut v_init_1580_: *mut LeanObject,
    mut v_self_1581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: u8 = 0;
    v_toArray_1582_ = lean_ctor_get(v_self_1581_, 1);
    lean_inc_ref(v_toArray_1582_);
    lean_dec_ref(v_self_1581_);
    v___x_1583_ = lean_array_get_size(v_toArray_1582_);
    v___x_1584_ = lean_unsigned_to_nat(0);
    v___x_1585_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1586_ = lean_nat_dec_lt(v___x_1584_, v___x_1583_);
    if v___x_1586_ == 0 {
        lean_dec_ref(v_toArray_1582_);
        lean_dec(v_f_1579_);
        return v_init_1580_;
    } else {
        let mut v___f_1587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: usize = 0;
        let mut v___x_1589_: usize = 0;
        let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
        v___f_1587_ = lean_alloc_closure(
            l_Lake_RBArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1587_, 0, v_f_1579_);
        v___x_1588_ = lean_usize_of_nat(v___x_1583_);
        v___x_1589_ = 0usize;
        v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b2_1591_: *mut LeanObject,
    mut v_00_u03c3_1592_: *mut LeanObject,
    mut v_00_u03b1_1593_: *mut LeanObject,
    mut v_cmp_1594_: *mut LeanObject,
    mut v_f_1595_: *mut LeanObject,
    mut v_init_1596_: *mut LeanObject,
    mut v_self_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lake_RBArray_foldr(
        v_00_u03b2_1591_,
        v_00_u03c3_1592_,
        v_00_u03b1_1593_,
        v_cmp_1594_,
        v_f_1595_,
        v_init_1596_,
        v_self_1597_,
    );
    lean_dec_ref(v_cmp_1594_);
    return v_res_1598_;
}
pub unsafe fn l_Lake_RBArray_foldrM___redArg(
    mut v_inst_1599_: *mut LeanObject,
    mut v_f_1600_: *mut LeanObject,
    mut v_init_1601_: *mut LeanObject,
    mut v_self_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    v_toArray_1603_ = lean_ctor_get(v_self_1602_, 1);
    lean_inc_ref(v_toArray_1603_);
    lean_dec_ref(v_self_1602_);
    v___x_1604_ = lean_array_get_size(v_toArray_1603_);
    v___x_1605_ = lean_unsigned_to_nat(0);
    v___x_1606_ = lean_nat_dec_lt(v___x_1605_, v___x_1604_);
    if v___x_1606_ == 0 {
        let mut v_toApplicative_1607_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1603_);
        lean_dec(v_f_1600_);
        v_toApplicative_1607_ = lean_ctor_get(v_inst_1599_, 0);
        lean_inc_ref(v_toApplicative_1607_);
        lean_dec_ref(v_inst_1599_);
        v_toPure_1608_ = lean_ctor_get(v_toApplicative_1607_, 1);
        lean_inc(v_toPure_1608_);
        lean_dec_ref(v_toApplicative_1607_);
        v___x_1609_ = lean_apply_2(v_toPure_1608_, lean_box(0), v_init_1601_);
        return v___x_1609_;
    } else {
        let mut v___x_1610_: usize = 0;
        let mut v___x_1611_: usize = 0;
        let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
        v___x_1610_ = lean_usize_of_nat(v___x_1604_);
        v___x_1611_ = 0usize;
        v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_m_1613_: *mut LeanObject,
    mut v_00_u03b2_1614_: *mut LeanObject,
    mut v_00_u03c3_1615_: *mut LeanObject,
    mut v_00_u03b1_1616_: *mut LeanObject,
    mut v_cmp_1617_: *mut LeanObject,
    mut v_inst_1618_: *mut LeanObject,
    mut v_f_1619_: *mut LeanObject,
    mut v_init_1620_: *mut LeanObject,
    mut v_self_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: u8 = 0;
    v_toArray_1622_ = lean_ctor_get(v_self_1621_, 1);
    lean_inc_ref(v_toArray_1622_);
    lean_dec_ref(v_self_1621_);
    v___x_1623_ = lean_array_get_size(v_toArray_1622_);
    v___x_1624_ = lean_unsigned_to_nat(0);
    v___x_1625_ = lean_nat_dec_lt(v___x_1624_, v___x_1623_);
    if v___x_1625_ == 0 {
        let mut v_toApplicative_1626_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1622_);
        lean_dec(v_f_1619_);
        v_toApplicative_1626_ = lean_ctor_get(v_inst_1618_, 0);
        lean_inc_ref(v_toApplicative_1626_);
        lean_dec_ref(v_inst_1618_);
        v_toPure_1627_ = lean_ctor_get(v_toApplicative_1626_, 1);
        lean_inc(v_toPure_1627_);
        lean_dec_ref(v_toApplicative_1626_);
        v___x_1628_ = lean_apply_2(v_toPure_1627_, lean_box(0), v_init_1620_);
        return v___x_1628_;
    } else {
        let mut v___x_1629_: usize = 0;
        let mut v___x_1630_: usize = 0;
        let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
        v___x_1629_ = lean_usize_of_nat(v___x_1623_);
        v___x_1630_ = 0usize;
        v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_m_1632_: *mut LeanObject,
    mut v_00_u03b2_1633_: *mut LeanObject,
    mut v_00_u03c3_1634_: *mut LeanObject,
    mut v_00_u03b1_1635_: *mut LeanObject,
    mut v_cmp_1636_: *mut LeanObject,
    mut v_inst_1637_: *mut LeanObject,
    mut v_f_1638_: *mut LeanObject,
    mut v_init_1639_: *mut LeanObject,
    mut v_self_1640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1641_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_cmp_1636_);
    return v_res_1641_;
}
pub unsafe fn l_Lake_RBArray_forM___redArg___lam__0(
    mut v_f_1642_: *mut LeanObject,
    mut v_x_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    v___x_1645_ = lean_apply_1(v_f_1642_, v___y_1644_);
    return v___x_1645_;
}
pub unsafe fn l_Lake_RBArray_forM___redArg(
    mut v_inst_1646_: *mut LeanObject,
    mut v_f_1647_: *mut LeanObject,
    mut v_self_1648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    v_toArray_1649_ = lean_ctor_get(v_self_1648_, 1);
    lean_inc_ref(v_toArray_1649_);
    lean_dec_ref(v_self_1648_);
    v___x_1650_ = lean_unsigned_to_nat(0);
    v___x_1651_ = lean_array_get_size(v_toArray_1649_);
    v___x_1652_ = lean_box(0);
    v___x_1653_ = lean_nat_dec_lt(v___x_1650_, v___x_1651_);
    if v___x_1653_ == 0 {
        let mut v_toApplicative_1654_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1649_);
        lean_dec(v_f_1647_);
        v_toApplicative_1654_ = lean_ctor_get(v_inst_1646_, 0);
        lean_inc_ref(v_toApplicative_1654_);
        lean_dec_ref(v_inst_1646_);
        v_toPure_1655_ = lean_ctor_get(v_toApplicative_1654_, 1);
        lean_inc(v_toPure_1655_);
        lean_dec_ref(v_toApplicative_1654_);
        v___x_1656_ = lean_apply_2(v_toPure_1655_, lean_box(0), v___x_1652_);
        return v___x_1656_;
    } else {
        let mut v___f_1657_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1658_: u8 = 0;
        v___f_1657_ = lean_alloc_closure(
            l_Lake_RBArray_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1657_, 0, v_f_1647_);
        v___x_1658_ = lean_nat_dec_le(v___x_1651_, v___x_1651_);
        if v___x_1658_ == 0 {
            if v___x_1653_ == 0 {
                let mut v_toApplicative_1659_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_1660_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_1657_);
                lean_dec_ref(v_toArray_1649_);
                v_toApplicative_1659_ = lean_ctor_get(v_inst_1646_, 0);
                lean_inc_ref(v_toApplicative_1659_);
                lean_dec_ref(v_inst_1646_);
                v_toPure_1660_ = lean_ctor_get(v_toApplicative_1659_, 1);
                lean_inc(v_toPure_1660_);
                lean_dec_ref(v_toApplicative_1659_);
                v___x_1661_ = lean_apply_2(v_toPure_1660_, lean_box(0), v___x_1652_);
                return v___x_1661_;
            } else {
                let mut v___x_1662_: usize = 0;
                let mut v___x_1663_: usize = 0;
                let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
                v___x_1662_ = 0usize;
                v___x_1663_ = lean_usize_of_nat(v___x_1651_);
                v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
            v___x_1665_ = 0usize;
            v___x_1666_ = lean_usize_of_nat(v___x_1651_);
            v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_m_1668_: *mut LeanObject,
    mut v_00_u03b2_1669_: *mut LeanObject,
    mut v_00_u03b1_1670_: *mut LeanObject,
    mut v_cmp_1671_: *mut LeanObject,
    mut v_inst_1672_: *mut LeanObject,
    mut v_f_1673_: *mut LeanObject,
    mut v_self_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    v_toArray_1675_ = lean_ctor_get(v_self_1674_, 1);
    lean_inc_ref(v_toArray_1675_);
    lean_dec_ref(v_self_1674_);
    v___x_1676_ = lean_unsigned_to_nat(0);
    v___x_1677_ = lean_array_get_size(v_toArray_1675_);
    v___x_1678_ = lean_box(0);
    v___x_1679_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
    if v___x_1679_ == 0 {
        let mut v_toApplicative_1680_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1675_);
        lean_dec(v_f_1673_);
        v_toApplicative_1680_ = lean_ctor_get(v_inst_1672_, 0);
        lean_inc_ref(v_toApplicative_1680_);
        lean_dec_ref(v_inst_1672_);
        v_toPure_1681_ = lean_ctor_get(v_toApplicative_1680_, 1);
        lean_inc(v_toPure_1681_);
        lean_dec_ref(v_toApplicative_1680_);
        v___x_1682_ = lean_apply_2(v_toPure_1681_, lean_box(0), v___x_1678_);
        return v___x_1682_;
    } else {
        let mut v___f_1683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: u8 = 0;
        v___f_1683_ = lean_alloc_closure(
            l_Lake_RBArray_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1683_, 0, v_f_1673_);
        v___x_1684_ = lean_nat_dec_le(v___x_1677_, v___x_1677_);
        if v___x_1684_ == 0 {
            if v___x_1679_ == 0 {
                let mut v_toApplicative_1685_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_1686_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_1683_);
                lean_dec_ref(v_toArray_1675_);
                v_toApplicative_1685_ = lean_ctor_get(v_inst_1672_, 0);
                lean_inc_ref(v_toApplicative_1685_);
                lean_dec_ref(v_inst_1672_);
                v_toPure_1686_ = lean_ctor_get(v_toApplicative_1685_, 1);
                lean_inc(v_toPure_1686_);
                lean_dec_ref(v_toApplicative_1685_);
                v___x_1687_ = lean_apply_2(v_toPure_1686_, lean_box(0), v___x_1678_);
                return v___x_1687_;
            } else {
                let mut v___x_1688_: usize = 0;
                let mut v___x_1689_: usize = 0;
                let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
                v___x_1688_ = 0usize;
                v___x_1689_ = lean_usize_of_nat(v___x_1677_);
                v___x_1690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
            v___x_1691_ = 0usize;
            v___x_1692_ = lean_usize_of_nat(v___x_1677_);
            v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_m_1694_: *mut LeanObject,
    mut v_00_u03b2_1695_: *mut LeanObject,
    mut v_00_u03b1_1696_: *mut LeanObject,
    mut v_cmp_1697_: *mut LeanObject,
    mut v_inst_1698_: *mut LeanObject,
    mut v_f_1699_: *mut LeanObject,
    mut v_self_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1701_: *mut LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lake_RBArray_forM(
        v_m_1694_,
        v_00_u03b2_1695_,
        v_00_u03b1_1696_,
        v_cmp_1697_,
        v_inst_1698_,
        v_f_1699_,
        v_self_1700_,
    );
    lean_dec_ref(v_cmp_1697_);
    return v_res_1701_;
}
pub unsafe fn l_Lake_RBArray_forIn___redArg___lam__0(
    mut v_f_1702_: *mut LeanObject,
    mut v_a_1703_: *mut LeanObject,
    mut v_x_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = lean_apply_2(v_f_1702_, v_a_1703_, v___y_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Lake_RBArray_forIn___redArg(
    mut v_inst_1707_: *mut LeanObject,
    mut v_self_1708_: *mut LeanObject,
    mut v_init_1709_: *mut LeanObject,
    mut v_f_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1713_: usize = 0;
    let mut v___x_1714_: usize = 0;
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v_toArray_1711_ = lean_ctor_get(v_self_1708_, 1);
    lean_inc_ref(v_toArray_1711_);
    lean_dec_ref(v_self_1708_);
    v___f_1712_ = lean_alloc_closure(
        l_Lake_RBArray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1712_, 0, v_f_1710_);
    v_sz_1713_ = lean_array_size(v_toArray_1711_);
    v___x_1714_ = 0usize;
    v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_m_1716_: *mut LeanObject,
    mut v_00_u03b1_1717_: *mut LeanObject,
    mut v_00_u03b2_1718_: *mut LeanObject,
    mut v_cmp_1719_: *mut LeanObject,
    mut v_00_u03c3_1720_: *mut LeanObject,
    mut v_inst_1721_: *mut LeanObject,
    mut v_self_1722_: *mut LeanObject,
    mut v_init_1723_: *mut LeanObject,
    mut v_f_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1727_: usize = 0;
    let mut v___x_1728_: usize = 0;
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    v_toArray_1725_ = lean_ctor_get(v_self_1722_, 1);
    lean_inc_ref(v_toArray_1725_);
    lean_dec_ref(v_self_1722_);
    v___f_1726_ = lean_alloc_closure(
        l_Lake_RBArray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1726_, 0, v_f_1724_);
    v_sz_1727_ = lean_array_size(v_toArray_1725_);
    v___x_1728_ = 0usize;
    v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_m_1730_: *mut LeanObject,
    mut v_00_u03b1_1731_: *mut LeanObject,
    mut v_00_u03b2_1732_: *mut LeanObject,
    mut v_cmp_1733_: *mut LeanObject,
    mut v_00_u03c3_1734_: *mut LeanObject,
    mut v_inst_1735_: *mut LeanObject,
    mut v_self_1736_: *mut LeanObject,
    mut v_init_1737_: *mut LeanObject,
    mut v_f_1738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1739_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_cmp_1733_);
    return v_res_1739_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0(
    mut v___y_1740_: *mut LeanObject,
    mut v_a_1741_: *mut LeanObject,
    mut v_x_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    v___x_1744_ = lean_apply_2(v___y_1740_, v_a_1741_, v___y_1743_);
    return v___x_1744_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1(
    mut v_inst_1745_: *mut LeanObject,
    mut v_00_u03b2_1746_: *mut LeanObject,
    mut v___y_1747_: *mut LeanObject,
    mut v___y_1748_: *mut LeanObject,
    mut v___y_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1752_: usize = 0;
    let mut v___x_1753_: usize = 0;
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    v_toArray_1750_ = lean_ctor_get(v___y_1747_, 1);
    lean_inc_ref(v_toArray_1750_);
    lean_dec_ref(v___y_1747_);
    v___f_1751_ = lean_alloc_closure(
        l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1751_, 0, v___y_1749_);
    v_sz_1752_ = lean_array_size(v_toArray_1750_);
    v___x_1753_ = 0usize;
    v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_inst_1755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1756_: *mut LeanObject = core::ptr::null_mut();
    v___f_1756_ = lean_alloc_closure(
        l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1756_, 0, v_inst_1755_);
    return v___f_1756_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(
    mut v_m_1757_: *mut LeanObject,
    mut v_00_u03b1_1758_: *mut LeanObject,
    mut v_00_u03b2_1759_: *mut LeanObject,
    mut v_cmp_1760_: *mut LeanObject,
    mut v_inst_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1762_: *mut LeanObject = core::ptr::null_mut();
    v___f_1762_ = lean_alloc_closure(
        l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1762_, 0, v_inst_1761_);
    return v___f_1762_;
}
pub unsafe fn l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___boxed(
    mut v_m_1763_: *mut LeanObject,
    mut v_00_u03b1_1764_: *mut LeanObject,
    mut v_00_u03b2_1765_: *mut LeanObject,
    mut v_cmp_1766_: *mut LeanObject,
    mut v_inst_1767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1768_: *mut LeanObject = core::ptr::null_mut();
    v_res_1768_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(
        v_m_1763_,
        v_00_u03b1_1764_,
        v_00_u03b2_1765_,
        v_cmp_1766_,
        v_inst_1767_,
    );
    lean_dec_ref(v_cmp_1766_);
    return v_res_1768_;
}
pub unsafe fn l_Lake_mkRBArray___redArg___lam__0(
    mut v_f_1769_: *mut LeanObject,
    mut v_cmp_1770_: *mut LeanObject,
    mut v_x1_1771_: *mut LeanObject,
    mut v_x2_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_x2_1772_);
    v___x_1773_ = lean_apply_1(v_f_1769_, v_x2_1772_);
    v___x_1774_ = l_Lake_RBArray_insert___redArg(v_cmp_1770_, v_x1_1771_, v___x_1773_, v_x2_1772_);
    return v___x_1774_;
}
pub unsafe fn l_Lake_mkRBArray___redArg(
    mut v_cmp_1775_: *mut LeanObject,
    mut v_f_1776_: *mut LeanObject,
    mut v_vs_1777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    v___x_1778_ = lean_array_get_size(v_vs_1777_);
    v___x_1779_ = l_Lake_RBArray_mkEmpty___redArg(v___x_1778_);
    v___x_1780_ = lean_unsigned_to_nat(0);
    v___x_1781_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1782_ = lean_nat_dec_lt(v___x_1780_, v___x_1778_);
    if v___x_1782_ == 0 {
        lean_dec_ref(v_vs_1777_);
        lean_dec(v_f_1776_);
        lean_dec_ref(v_cmp_1775_);
        return v___x_1779_;
    } else {
        let mut v___f_1783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1784_: u8 = 0;
        v___f_1783_ = lean_alloc_closure(
            l_Lake_mkRBArray___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_1783_, 0, v_f_1776_);
        lean_closure_set(v___f_1783_, 1, v_cmp_1775_);
        v___x_1784_ = lean_nat_dec_le(v___x_1778_, v___x_1778_);
        if v___x_1784_ == 0 {
            if v___x_1782_ == 0 {
                lean_dec_ref(v___f_1783_);
                lean_dec_ref(v_vs_1777_);
                return v___x_1779_;
            } else {
                let mut v___x_1785_: usize = 0;
                let mut v___x_1786_: usize = 0;
                let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
                v___x_1785_ = 0usize;
                v___x_1786_ = lean_usize_of_nat(v___x_1778_);
                v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
            v___x_1788_ = 0usize;
            v___x_1789_ = lean_usize_of_nat(v___x_1778_);
            v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b2_1791_: *mut LeanObject,
    mut v_00_u03b1_1792_: *mut LeanObject,
    mut v_cmp_1793_: *mut LeanObject,
    mut v_f_1794_: *mut LeanObject,
    mut v_vs_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    v___x_1796_ = lean_array_get_size(v_vs_1795_);
    v___x_1797_ = l_Lake_RBArray_mkEmpty___redArg(v___x_1796_);
    v___x_1798_ = lean_unsigned_to_nat(0);
    v___x_1799_ = l_Lake_RBArray_all___redArg___closed__9;
    v___x_1800_ = lean_nat_dec_lt(v___x_1798_, v___x_1796_);
    if v___x_1800_ == 0 {
        lean_dec_ref(v_vs_1795_);
        lean_dec(v_f_1794_);
        lean_dec_ref(v_cmp_1793_);
        return v___x_1797_;
    } else {
        let mut v___f_1801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: u8 = 0;
        v___f_1801_ = lean_alloc_closure(
            l_Lake_mkRBArray___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_1801_, 0, v_f_1794_);
        lean_closure_set(v___f_1801_, 1, v_cmp_1793_);
        v___x_1802_ = lean_nat_dec_le(v___x_1796_, v___x_1796_);
        if v___x_1802_ == 0 {
            if v___x_1800_ == 0 {
                lean_dec_ref(v___f_1801_);
                lean_dec_ref(v_vs_1795_);
                return v___x_1797_;
            } else {
                let mut v___x_1803_: usize = 0;
                let mut v___x_1804_: usize = 0;
                let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
                v___x_1803_ = 0usize;
                v___x_1804_ = lean_usize_of_nat(v___x_1796_);
                v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
            v___x_1806_ = 0usize;
            v___x_1807_ = lean_usize_of_nat(v___x_1796_);
            v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
pub unsafe fn runtime_initialize_Lake_Util_RBArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_RBArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_RBArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_RBArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_RBArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_RBArray(builtin);
}
