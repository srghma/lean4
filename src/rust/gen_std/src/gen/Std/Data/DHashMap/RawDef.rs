// Lean compiler output
// Module: Std.Data.DHashMap.RawDef
// Imports: Std.Data.DHashMap.Internal.AssocList.Basic Init.Data.Array.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    initialize_Std_Data_DHashMap_Internal_AssocList_Basic,
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go,
    l_Std_DHashMap_Internal_AssocList_foldlM___redArg,
    runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic,
};
pub static l_Std_DHashMap_Raw_fold___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_fold___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_fold___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_fold___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_all___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_all___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_all___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Raw_foldM___redArg___lam__0(
    mut v_inst_405_: *mut crate::leanh::LeanObject,
    mut v_f_406_: *mut crate::leanh::LeanObject,
    mut v_acc_407_: *mut crate::leanh::LeanObject,
    mut v_l_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_409_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_405_,
        v_f_406_,
        v_acc_407_,
        v_l_408_,
    );
    return v___x_409_;
}
pub unsafe fn l_Std_DHashMap_Raw_foldM___redArg(
    mut v_inst_410_: *mut crate::leanh::LeanObject,
    mut v_f_411_: *mut crate::leanh::LeanObject,
    mut v_init_412_: *mut crate::leanh::LeanObject,
    mut v_b_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: u8 = 0;
    v_buckets_414_ = crate::leanh::lean_ctor_get(v_b_413_, 1);
    crate::leanh::lean_inc_ref(v_buckets_414_);
    crate::leanh::lean_dec_ref(v_b_413_);
    v___x_415_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_416_ = lean_array_get_size(v_buckets_414_);
    v___x_417_ = lean_nat_dec_lt(v___x_415_, v___x_416_);
    if v___x_417_ == 0 {
        let mut v_toApplicative_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_414_);
        crate::leanh::lean_dec(v_f_411_);
        v_toApplicative_418_ = crate::leanh::lean_ctor_get(v_inst_410_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_418_);
        crate::leanh::lean_dec_ref(v_inst_410_);
        v_toPure_419_ = crate::leanh::lean_ctor_get(v_toApplicative_418_, 1);
        crate::leanh::lean_inc(v_toPure_419_);
        crate::leanh::lean_dec_ref(v_toApplicative_418_);
        v___x_420_ =
            crate::leanh::lean_apply_2(v_toPure_419_, crate::leanh::lean_box(0), v_init_412_);
        return v___x_420_;
    } else {
        let mut v___f_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_422_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_410_);
        v___f_421_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_421_, 0, v_inst_410_);
        crate::leanh::lean_closure_set(v___f_421_, 1, v_f_411_);
        v___x_422_ = lean_nat_dec_le(v___x_416_, v___x_416_);
        if v___x_422_ == 0 {
            if v___x_417_ == 0 {
                let mut v_toApplicative_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_421_);
                crate::leanh::lean_dec_ref(v_buckets_414_);
                v_toApplicative_423_ = crate::leanh::lean_ctor_get(v_inst_410_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_423_);
                crate::leanh::lean_dec_ref(v_inst_410_);
                v_toPure_424_ = crate::leanh::lean_ctor_get(v_toApplicative_423_, 1);
                crate::leanh::lean_inc(v_toPure_424_);
                crate::leanh::lean_dec_ref(v_toApplicative_423_);
                v___x_425_ = crate::leanh::lean_apply_2(
                    v_toPure_424_,
                    crate::leanh::lean_box(0),
                    v_init_412_,
                );
                return v___x_425_;
            } else {
                let mut v___x_426_: usize = 0;
                let mut v___x_427_: usize = 0;
                let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_426_ = 0usize;
                v___x_427_ = lean_usize_of_nat(v___x_416_);
                v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_410_,
                    v___f_421_,
                    v_buckets_414_,
                    v___x_426_,
                    v___x_427_,
                    v_init_412_,
                );
                return v___x_428_;
            }
        } else {
            let mut v___x_429_: usize = 0;
            let mut v___x_430_: usize = 0;
            let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_429_ = 0usize;
            v___x_430_ = lean_usize_of_nat(v___x_416_);
            v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_410_,
                v___f_421_,
                v_buckets_414_,
                v___x_429_,
                v___x_430_,
                v_init_412_,
            );
            return v___x_431_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_foldM(
    mut v_00_u03b1_432_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_434_: *mut crate::leanh::LeanObject,
    mut v_m_435_: *mut crate::leanh::LeanObject,
    mut v_inst_436_: *mut crate::leanh::LeanObject,
    mut v_f_437_: *mut crate::leanh::LeanObject,
    mut v_init_438_: *mut crate::leanh::LeanObject,
    mut v_b_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    v_buckets_440_ = crate::leanh::lean_ctor_get(v_b_439_, 1);
    crate::leanh::lean_inc_ref(v_buckets_440_);
    crate::leanh::lean_dec_ref(v_b_439_);
    v___x_441_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_442_ = lean_array_get_size(v_buckets_440_);
    v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
    if v___x_443_ == 0 {
        let mut v_toApplicative_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_440_);
        crate::leanh::lean_dec(v_f_437_);
        v_toApplicative_444_ = crate::leanh::lean_ctor_get(v_inst_436_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_444_);
        crate::leanh::lean_dec_ref(v_inst_436_);
        v_toPure_445_ = crate::leanh::lean_ctor_get(v_toApplicative_444_, 1);
        crate::leanh::lean_inc(v_toPure_445_);
        crate::leanh::lean_dec_ref(v_toApplicative_444_);
        v___x_446_ =
            crate::leanh::lean_apply_2(v_toPure_445_, crate::leanh::lean_box(0), v_init_438_);
        return v___x_446_;
    } else {
        let mut v___f_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_436_);
        v___f_447_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_447_, 0, v_inst_436_);
        crate::leanh::lean_closure_set(v___f_447_, 1, v_f_437_);
        v___x_448_ = lean_nat_dec_le(v___x_442_, v___x_442_);
        if v___x_448_ == 0 {
            if v___x_443_ == 0 {
                let mut v_toApplicative_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_447_);
                crate::leanh::lean_dec_ref(v_buckets_440_);
                v_toApplicative_449_ = crate::leanh::lean_ctor_get(v_inst_436_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_449_);
                crate::leanh::lean_dec_ref(v_inst_436_);
                v_toPure_450_ = crate::leanh::lean_ctor_get(v_toApplicative_449_, 1);
                crate::leanh::lean_inc(v_toPure_450_);
                crate::leanh::lean_dec_ref(v_toApplicative_449_);
                v___x_451_ = crate::leanh::lean_apply_2(
                    v_toPure_450_,
                    crate::leanh::lean_box(0),
                    v_init_438_,
                );
                return v___x_451_;
            } else {
                let mut v___x_452_: usize = 0;
                let mut v___x_453_: usize = 0;
                let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_452_ = 0usize;
                v___x_453_ = lean_usize_of_nat(v___x_442_);
                v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_436_,
                    v___f_447_,
                    v_buckets_440_,
                    v___x_452_,
                    v___x_453_,
                    v_init_438_,
                );
                return v___x_454_;
            }
        } else {
            let mut v___x_455_: usize = 0;
            let mut v___x_456_: usize = 0;
            let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_455_ = 0usize;
            v___x_456_ = lean_usize_of_nat(v___x_442_);
            v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_436_,
                v___f_447_,
                v_buckets_440_,
                v___x_455_,
                v___x_456_,
                v_init_438_,
            );
            return v___x_457_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_fold___redArg___lam__0(
    mut v_f_458_: *mut crate::leanh::LeanObject,
    mut v_x1_459_: *mut crate::leanh::LeanObject,
    mut v_x2_460_: *mut crate::leanh::LeanObject,
    mut v_x3_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_462_ = crate::leanh::lean_apply_3(v_f_458_, v_x1_459_, v_x2_460_, v_x3_461_);
    return v___x_462_;
}
pub unsafe fn l_Std_DHashMap_Raw_fold___redArg___lam__1(
    mut v___x_463_: *mut crate::leanh::LeanObject,
    mut v___f_464_: *mut crate::leanh::LeanObject,
    mut v_acc_465_: *mut crate::leanh::LeanObject,
    mut v_l_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_463_, v___f_464_, v_acc_465_, v_l_466_,
    );
    return v___x_467_;
}
pub unsafe fn l_Std_DHashMap_Raw_fold___redArg(
    mut v_f_487_: *mut crate::leanh::LeanObject,
    mut v_init_488_: *mut crate::leanh::LeanObject,
    mut v_b_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    v___x_490_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_491_ = crate::leanh::lean_ctor_get(v_b_489_, 1);
    crate::leanh::lean_inc_ref(v_buckets_491_);
    crate::leanh::lean_dec_ref(v_b_489_);
    v___x_492_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_493_ = lean_array_get_size(v_buckets_491_);
    v___x_494_ = lean_nat_dec_lt(v___x_492_, v___x_493_);
    if v___x_494_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_491_);
        crate::leanh::lean_dec(v_f_487_);
        return v_init_488_;
    } else {
        let mut v___f_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_497_: u8 = 0;
        v___f_495_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_495_, 0, v_f_487_);
        v___f_496_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_496_, 0, v___x_490_);
        crate::leanh::lean_closure_set(v___f_496_, 1, v___f_495_);
        v___x_497_ = lean_nat_dec_le(v___x_493_, v___x_493_);
        if v___x_497_ == 0 {
            if v___x_494_ == 0 {
                crate::leanh::lean_dec_ref(v___f_496_);
                crate::leanh::lean_dec_ref(v_buckets_491_);
                return v_init_488_;
            } else {
                let mut v___x_498_: usize = 0;
                let mut v___x_499_: usize = 0;
                let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_498_ = 0usize;
                v___x_499_ = lean_usize_of_nat(v___x_493_);
                v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_490_,
                    v___f_496_,
                    v_buckets_491_,
                    v___x_498_,
                    v___x_499_,
                    v_init_488_,
                );
                return v___x_500_;
            }
        } else {
            let mut v___x_501_: usize = 0;
            let mut v___x_502_: usize = 0;
            let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_501_ = 0usize;
            v___x_502_ = lean_usize_of_nat(v___x_493_);
            v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_490_,
                v___f_496_,
                v_buckets_491_,
                v___x_501_,
                v___x_502_,
                v_init_488_,
            );
            return v___x_503_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_fold(
    mut v_00_u03b1_504_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_505_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_506_: *mut crate::leanh::LeanObject,
    mut v_f_507_: *mut crate::leanh::LeanObject,
    mut v_init_508_: *mut crate::leanh::LeanObject,
    mut v_b_509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: u8 = 0;
    v___x_510_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_511_ = crate::leanh::lean_ctor_get(v_b_509_, 1);
    crate::leanh::lean_inc_ref(v_buckets_511_);
    crate::leanh::lean_dec_ref(v_b_509_);
    v___x_512_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_513_ = lean_array_get_size(v_buckets_511_);
    v___x_514_ = lean_nat_dec_lt(v___x_512_, v___x_513_);
    if v___x_514_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_511_);
        crate::leanh::lean_dec(v_f_507_);
        return v_init_508_;
    } else {
        let mut v___f_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_517_: u8 = 0;
        v___f_515_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_515_, 0, v_f_507_);
        v___f_516_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_516_, 0, v___x_510_);
        crate::leanh::lean_closure_set(v___f_516_, 1, v___f_515_);
        v___x_517_ = lean_nat_dec_le(v___x_513_, v___x_513_);
        if v___x_517_ == 0 {
            if v___x_514_ == 0 {
                crate::leanh::lean_dec_ref(v___f_516_);
                crate::leanh::lean_dec_ref(v_buckets_511_);
                return v_init_508_;
            } else {
                let mut v___x_518_: usize = 0;
                let mut v___x_519_: usize = 0;
                let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_518_ = 0usize;
                v___x_519_ = lean_usize_of_nat(v___x_513_);
                v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_510_,
                    v___f_516_,
                    v_buckets_511_,
                    v___x_518_,
                    v___x_519_,
                    v_init_508_,
                );
                return v___x_520_;
            }
        } else {
            let mut v___x_521_: usize = 0;
            let mut v___x_522_: usize = 0;
            let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_521_ = 0usize;
            v___x_522_ = lean_usize_of_nat(v___x_513_);
            v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_510_,
                v___f_516_,
                v_buckets_511_,
                v___x_521_,
                v___x_522_,
                v_init_508_,
            );
            return v___x_523_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_forM___redArg___lam__0(
    mut v_f_524_: *mut crate::leanh::LeanObject,
    mut v_x_525_: *mut crate::leanh::LeanObject,
    mut v___y_526_: *mut crate::leanh::LeanObject,
    mut v___y_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_528_ = crate::leanh::lean_apply_2(v_f_524_, v___y_526_, v___y_527_);
    return v___x_528_;
}
pub unsafe fn l_Std_DHashMap_Raw_forM___redArg___lam__1(
    mut v_inst_529_: *mut crate::leanh::LeanObject,
    mut v___f_530_: *mut crate::leanh::LeanObject,
    mut v_x_531_: *mut crate::leanh::LeanObject,
    mut v___y_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = crate::leanh::lean_box(0);
    v___x_534_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_529_,
        v___f_530_,
        v___x_533_,
        v___y_532_,
    );
    return v___x_534_;
}
pub unsafe fn l_Std_DHashMap_Raw_forM___redArg(
    mut v_inst_535_: *mut crate::leanh::LeanObject,
    mut v_f_536_: *mut crate::leanh::LeanObject,
    mut v_b_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: u8 = 0;
    v_buckets_538_ = crate::leanh::lean_ctor_get(v_b_537_, 1);
    crate::leanh::lean_inc_ref(v_buckets_538_);
    crate::leanh::lean_dec_ref(v_b_537_);
    v___x_539_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_540_ = lean_array_get_size(v_buckets_538_);
    v___x_541_ = crate::leanh::lean_box(0);
    v___x_542_ = lean_nat_dec_lt(v___x_539_, v___x_540_);
    if v___x_542_ == 0 {
        let mut v_toApplicative_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_538_);
        crate::leanh::lean_dec(v_f_536_);
        v_toApplicative_543_ = crate::leanh::lean_ctor_get(v_inst_535_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_543_);
        crate::leanh::lean_dec_ref(v_inst_535_);
        v_toPure_544_ = crate::leanh::lean_ctor_get(v_toApplicative_543_, 1);
        crate::leanh::lean_inc(v_toPure_544_);
        crate::leanh::lean_dec_ref(v_toApplicative_543_);
        v___x_545_ =
            crate::leanh::lean_apply_2(v_toPure_544_, crate::leanh::lean_box(0), v___x_541_);
        return v___x_545_;
    } else {
        let mut v___f_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_548_: u8 = 0;
        v___f_546_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_546_, 0, v_f_536_);
        crate::leanh::lean_inc_ref(v_inst_535_);
        v___f_547_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_547_, 0, v_inst_535_);
        crate::leanh::lean_closure_set(v___f_547_, 1, v___f_546_);
        v___x_548_ = lean_nat_dec_le(v___x_540_, v___x_540_);
        if v___x_548_ == 0 {
            if v___x_542_ == 0 {
                let mut v_toApplicative_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_547_);
                crate::leanh::lean_dec_ref(v_buckets_538_);
                v_toApplicative_549_ = crate::leanh::lean_ctor_get(v_inst_535_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_549_);
                crate::leanh::lean_dec_ref(v_inst_535_);
                v_toPure_550_ = crate::leanh::lean_ctor_get(v_toApplicative_549_, 1);
                crate::leanh::lean_inc(v_toPure_550_);
                crate::leanh::lean_dec_ref(v_toApplicative_549_);
                v___x_551_ = crate::leanh::lean_apply_2(
                    v_toPure_550_,
                    crate::leanh::lean_box(0),
                    v___x_541_,
                );
                return v___x_551_;
            } else {
                let mut v___x_552_: usize = 0;
                let mut v___x_553_: usize = 0;
                let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_552_ = 0usize;
                v___x_553_ = lean_usize_of_nat(v___x_540_);
                v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_535_,
                    v___f_547_,
                    v_buckets_538_,
                    v___x_552_,
                    v___x_553_,
                    v___x_541_,
                );
                return v___x_554_;
            }
        } else {
            let mut v___x_555_: usize = 0;
            let mut v___x_556_: usize = 0;
            let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_555_ = 0usize;
            v___x_556_ = lean_usize_of_nat(v___x_540_);
            v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_535_,
                v___f_547_,
                v_buckets_538_,
                v___x_555_,
                v___x_556_,
                v___x_541_,
            );
            return v___x_557_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_forM(
    mut v_00_u03b1_558_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_559_: *mut crate::leanh::LeanObject,
    mut v_m_560_: *mut crate::leanh::LeanObject,
    mut v_inst_561_: *mut crate::leanh::LeanObject,
    mut v_f_562_: *mut crate::leanh::LeanObject,
    mut v_b_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: u8 = 0;
    v_buckets_564_ = crate::leanh::lean_ctor_get(v_b_563_, 1);
    crate::leanh::lean_inc_ref(v_buckets_564_);
    crate::leanh::lean_dec_ref(v_b_563_);
    v___x_565_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_566_ = lean_array_get_size(v_buckets_564_);
    v___x_567_ = crate::leanh::lean_box(0);
    v___x_568_ = lean_nat_dec_lt(v___x_565_, v___x_566_);
    if v___x_568_ == 0 {
        let mut v_toApplicative_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_564_);
        crate::leanh::lean_dec(v_f_562_);
        v_toApplicative_569_ = crate::leanh::lean_ctor_get(v_inst_561_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_569_);
        crate::leanh::lean_dec_ref(v_inst_561_);
        v_toPure_570_ = crate::leanh::lean_ctor_get(v_toApplicative_569_, 1);
        crate::leanh::lean_inc(v_toPure_570_);
        crate::leanh::lean_dec_ref(v_toApplicative_569_);
        v___x_571_ =
            crate::leanh::lean_apply_2(v_toPure_570_, crate::leanh::lean_box(0), v___x_567_);
        return v___x_571_;
    } else {
        let mut v___f_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_574_: u8 = 0;
        v___f_572_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_572_, 0, v_f_562_);
        crate::leanh::lean_inc_ref(v_inst_561_);
        v___f_573_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_573_, 0, v_inst_561_);
        crate::leanh::lean_closure_set(v___f_573_, 1, v___f_572_);
        v___x_574_ = lean_nat_dec_le(v___x_566_, v___x_566_);
        if v___x_574_ == 0 {
            if v___x_568_ == 0 {
                let mut v_toApplicative_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_573_);
                crate::leanh::lean_dec_ref(v_buckets_564_);
                v_toApplicative_575_ = crate::leanh::lean_ctor_get(v_inst_561_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_575_);
                crate::leanh::lean_dec_ref(v_inst_561_);
                v_toPure_576_ = crate::leanh::lean_ctor_get(v_toApplicative_575_, 1);
                crate::leanh::lean_inc(v_toPure_576_);
                crate::leanh::lean_dec_ref(v_toApplicative_575_);
                v___x_577_ = crate::leanh::lean_apply_2(
                    v_toPure_576_,
                    crate::leanh::lean_box(0),
                    v___x_567_,
                );
                return v___x_577_;
            } else {
                let mut v___x_578_: usize = 0;
                let mut v___x_579_: usize = 0;
                let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_578_ = 0usize;
                v___x_579_ = lean_usize_of_nat(v___x_566_);
                v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_561_,
                    v___f_573_,
                    v_buckets_564_,
                    v___x_578_,
                    v___x_579_,
                    v___x_567_,
                );
                return v___x_580_;
            }
        } else {
            let mut v___x_581_: usize = 0;
            let mut v___x_582_: usize = 0;
            let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_581_ = 0usize;
            v___x_582_ = lean_usize_of_nat(v___x_566_);
            v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_561_,
                v___f_573_,
                v_buckets_564_,
                v___x_581_,
                v___x_582_,
                v___x_567_,
            );
            return v___x_583_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_forIn___redArg___lam__0(
    mut v_inst_584_: *mut crate::leanh::LeanObject,
    mut v_f_585_: *mut crate::leanh::LeanObject,
    mut v_a_586_: *mut crate::leanh::LeanObject,
    mut v_x_587_: *mut crate::leanh::LeanObject,
    mut v___y_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_584_, v_f_585_, v_a_586_, v___y_588_);
    return v___x_589_;
}
pub unsafe fn l_Std_DHashMap_Raw_forIn___redArg(
    mut v_inst_590_: *mut crate::leanh::LeanObject,
    mut v_f_591_: *mut crate::leanh::LeanObject,
    mut v_init_592_: *mut crate::leanh::LeanObject,
    mut v_b_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_596_: usize = 0;
    let mut v___x_597_: usize = 0;
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_594_ = crate::leanh::lean_ctor_get(v_b_593_, 1);
    crate::leanh::lean_inc_ref(v_buckets_594_);
    crate::leanh::lean_dec_ref(v_b_593_);
    crate::leanh::lean_inc_ref(v_inst_590_);
    v___f_595_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_595_, 0, v_inst_590_);
    crate::leanh::lean_closure_set(v___f_595_, 1, v_f_591_);
    v_sz_596_ = lean_array_size(v_buckets_594_);
    v___x_597_ = 0usize;
    v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_590_,
        v_buckets_594_,
        v___f_595_,
        v_sz_596_,
        v___x_597_,
        v_init_592_,
    );
    return v___x_598_;
}
pub unsafe fn l_Std_DHashMap_Raw_forIn(
    mut v_00_u03b1_599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_600_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_601_: *mut crate::leanh::LeanObject,
    mut v_m_602_: *mut crate::leanh::LeanObject,
    mut v_inst_603_: *mut crate::leanh::LeanObject,
    mut v_f_604_: *mut crate::leanh::LeanObject,
    mut v_init_605_: *mut crate::leanh::LeanObject,
    mut v_b_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_609_: usize = 0;
    let mut v___x_610_: usize = 0;
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_607_ = crate::leanh::lean_ctor_get(v_b_606_, 1);
    crate::leanh::lean_inc_ref(v_buckets_607_);
    crate::leanh::lean_dec_ref(v_b_606_);
    crate::leanh::lean_inc_ref(v_inst_603_);
    v___f_608_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_608_, 0, v_inst_603_);
    crate::leanh::lean_closure_set(v___f_608_, 1, v_f_604_);
    v_sz_609_ = lean_array_size(v_buckets_607_);
    v___x_610_ = 0usize;
    v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_603_,
        v_buckets_607_,
        v___f_608_,
        v_sz_609_,
        v___x_610_,
        v_init_605_,
    );
    return v___x_611_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0(
    mut v_f_612_: *mut crate::leanh::LeanObject,
    mut v_x_613_: *mut crate::leanh::LeanObject,
    mut v___y_614_: *mut crate::leanh::LeanObject,
    mut v___y_615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_616_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_616_, 0, v___y_614_);
    crate::leanh::lean_ctor_set(v___x_616_, 1, v___y_615_);
    v___x_617_ = crate::leanh::lean_apply_1(v_f_612_, v___x_616_);
    return v___x_617_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2(
    mut v_inst_618_: *mut crate::leanh::LeanObject,
    mut v_m_619_: *mut crate::leanh::LeanObject,
    mut v_f_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    v_buckets_621_ = crate::leanh::lean_ctor_get(v_m_619_, 1);
    crate::leanh::lean_inc_ref(v_buckets_621_);
    crate::leanh::lean_dec_ref(v_m_619_);
    v___x_622_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_623_ = lean_array_get_size(v_buckets_621_);
    v___x_624_ = crate::leanh::lean_box(0);
    v___x_625_ = lean_nat_dec_lt(v___x_622_, v___x_623_);
    if v___x_625_ == 0 {
        let mut v_toApplicative_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_621_);
        crate::leanh::lean_dec(v_f_620_);
        v_toApplicative_626_ = crate::leanh::lean_ctor_get(v_inst_618_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_626_);
        crate::leanh::lean_dec_ref(v_inst_618_);
        v_toPure_627_ = crate::leanh::lean_ctor_get(v_toApplicative_626_, 1);
        crate::leanh::lean_inc(v_toPure_627_);
        crate::leanh::lean_dec_ref(v_toApplicative_626_);
        v___x_628_ =
            crate::leanh::lean_apply_2(v_toPure_627_, crate::leanh::lean_box(0), v___x_624_);
        return v___x_628_;
    } else {
        let mut v___f_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_631_: u8 = 0;
        v___f_629_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_629_, 0, v_f_620_);
        crate::leanh::lean_inc_ref(v_inst_618_);
        v___f_630_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_630_, 0, v_inst_618_);
        crate::leanh::lean_closure_set(v___f_630_, 1, v___f_629_);
        v___x_631_ = lean_nat_dec_le(v___x_623_, v___x_623_);
        if v___x_631_ == 0 {
            if v___x_625_ == 0 {
                let mut v_toApplicative_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_630_);
                crate::leanh::lean_dec_ref(v_buckets_621_);
                v_toApplicative_632_ = crate::leanh::lean_ctor_get(v_inst_618_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_632_);
                crate::leanh::lean_dec_ref(v_inst_618_);
                v_toPure_633_ = crate::leanh::lean_ctor_get(v_toApplicative_632_, 1);
                crate::leanh::lean_inc(v_toPure_633_);
                crate::leanh::lean_dec_ref(v_toApplicative_632_);
                v___x_634_ = crate::leanh::lean_apply_2(
                    v_toPure_633_,
                    crate::leanh::lean_box(0),
                    v___x_624_,
                );
                return v___x_634_;
            } else {
                let mut v___x_635_: usize = 0;
                let mut v___x_636_: usize = 0;
                let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_635_ = 0usize;
                v___x_636_ = lean_usize_of_nat(v___x_623_);
                v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_618_,
                    v___f_630_,
                    v_buckets_621_,
                    v___x_635_,
                    v___x_636_,
                    v___x_624_,
                );
                return v___x_637_;
            }
        } else {
            let mut v___x_638_: usize = 0;
            let mut v___x_639_: usize = 0;
            let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_638_ = 0usize;
            v___x_639_ = lean_usize_of_nat(v___x_623_);
            v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_618_,
                v___f_630_,
                v_buckets_621_,
                v___x_638_,
                v___x_639_,
                v___x_624_,
            );
            return v___x_640_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg(
    mut v_inst_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_642_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_642_, 0, v_inst_641_);
    return v___f_642_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForMSigmaOfMonad(
    mut v_00_u03b1_643_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_644_: *mut crate::leanh::LeanObject,
    mut v_m_645_: *mut crate::leanh::LeanObject,
    mut v_inst_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_647_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_647_, 0, v_inst_646_);
    return v___f_647_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0(
    mut v_f_648_: *mut crate::leanh::LeanObject,
    mut v_a_649_: *mut crate::leanh::LeanObject,
    mut v_b_650_: *mut crate::leanh::LeanObject,
    mut v_acc_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_652_, 0, v_a_649_);
    crate::leanh::lean_ctor_set(v___x_652_, 1, v_b_650_);
    v___x_653_ = crate::leanh::lean_apply_2(v_f_648_, v___x_652_, v_acc_651_);
    return v___x_653_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(
    mut v_inst_654_: *mut crate::leanh::LeanObject,
    mut v___f_655_: *mut crate::leanh::LeanObject,
    mut v_a_656_: *mut crate::leanh::LeanObject,
    mut v_x_657_: *mut crate::leanh::LeanObject,
    mut v___y_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_654_, v___f_655_, v_a_656_, v___y_658_);
    return v___x_659_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(
    mut v_inst_660_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_661_: *mut crate::leanh::LeanObject,
    mut v_m_662_: *mut crate::leanh::LeanObject,
    mut v_init_663_: *mut crate::leanh::LeanObject,
    mut v_f_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_668_: usize = 0;
    let mut v___x_669_: usize = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_665_ = crate::leanh::lean_ctor_get(v_m_662_, 1);
    crate::leanh::lean_inc_ref(v_buckets_665_);
    crate::leanh::lean_dec_ref(v_m_662_);
    v___f_666_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_666_, 0, v_f_664_);
    crate::leanh::lean_inc_ref(v_inst_660_);
    v___f_667_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_667_, 0, v_inst_660_);
    crate::leanh::lean_closure_set(v___f_667_, 1, v___f_666_);
    v_sz_668_ = lean_array_size(v_buckets_665_);
    v___x_669_ = 0usize;
    v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_660_,
        v_buckets_665_,
        v___f_667_,
        v_sz_668_,
        v___x_669_,
        v_init_663_,
    );
    return v___x_670_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg(
    mut v_inst_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_672_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_672_, 0, v_inst_671_);
    return v___f_672_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad(
    mut v_00_u03b1_673_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_674_: *mut crate::leanh::LeanObject,
    mut v_m_675_: *mut crate::leanh::LeanObject,
    mut v_inst_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_677_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_677_, 0, v_inst_676_);
    return v___f_677_;
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg___lam__0(
    mut v_p_678_: *mut crate::leanh::LeanObject,
    mut v___x_679_: *mut crate::leanh::LeanObject,
    mut v___x_680_: *mut crate::leanh::LeanObject,
    mut v_a_681_: *mut crate::leanh::LeanObject,
    mut v_b_682_: *mut crate::leanh::LeanObject,
    mut v_acc_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    v___x_684_ = crate::leanh::lean_apply_2(v_p_678_, v_a_681_, v_b_682_);
    v___x_685_ = (crate::leanh::lean_unbox(v___x_684_) as u8);
    if v___x_685_ == 0 {
        let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_680_);
        v___x_686_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_684_);
        v___x_687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_687_, 0, v___x_686_);
        crate::leanh::lean_ctor_set(v___x_687_, 1, v___x_679_);
        v___x_688_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_688_, 0, v___x_687_);
        return v___x_688_;
    } else {
        let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_689_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_689_, 0, v___x_680_);
        return v___x_689_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg___lam__0___boxed(
    mut v_p_690_: *mut crate::leanh::LeanObject,
    mut v___x_691_: *mut crate::leanh::LeanObject,
    mut v___x_692_: *mut crate::leanh::LeanObject,
    mut v_a_693_: *mut crate::leanh::LeanObject,
    mut v_b_694_: *mut crate::leanh::LeanObject,
    mut v_acc_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Std_DHashMap_Raw_all___redArg___lam__0(
        v_p_690_, v___x_691_, v___x_692_, v_a_693_, v_b_694_, v_acc_695_,
    );
    crate::leanh::lean_dec_ref(v_acc_695_);
    return v_res_696_;
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg___lam__1(
    mut v___x_697_: *mut crate::leanh::LeanObject,
    mut v___f_698_: *mut crate::leanh::LeanObject,
    mut v_a_699_: *mut crate::leanh::LeanObject,
    mut v_x_700_: *mut crate::leanh::LeanObject,
    mut v___y_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_702_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_697_, v___f_698_, v_a_699_, v___y_701_);
    return v___x_702_;
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg(
    mut v_m_706_: *mut crate::leanh::LeanObject,
    mut v_p_707_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_714_: usize = 0;
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_709_ = crate::leanh::lean_ctor_get(v_m_706_, 1);
    crate::leanh::lean_inc_ref(v_buckets_709_);
    crate::leanh::lean_dec_ref(v_m_706_);
    v___x_710_ = crate::leanh::lean_box(0);
    v___x_711_ = l_Std_DHashMap_Raw_all___redArg___closed__0;
    v___f_712_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_712_, 0, v_p_707_);
    crate::leanh::lean_closure_set(v___f_712_, 1, v___x_710_);
    crate::leanh::lean_closure_set(v___f_712_, 2, v___x_711_);
    v___f_713_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_713_, 0, v___x_708_);
    crate::leanh::lean_closure_set(v___f_713_, 1, v___f_712_);
    v_sz_714_ = lean_array_size(v_buckets_709_);
    v___x_715_ = 0usize;
    v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_708_,
        v_buckets_709_,
        v___f_713_,
        v_sz_714_,
        v___x_715_,
        v___x_711_,
    );
    v_fst_717_ = crate::leanh::lean_ctor_get(v___x_716_, 0);
    crate::leanh::lean_inc(v_fst_717_);
    crate::leanh::lean_dec(v___x_716_);
    if crate::leanh::lean_obj_tag(v_fst_717_) == 0 {
        let mut v___x_718_: u8 = 0;
        v___x_718_ = 1;
        return v___x_718_;
    } else {
        let mut v_val_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_720_: u8 = 0;
        v_val_719_ = crate::leanh::lean_ctor_get(v_fst_717_, 0);
        crate::leanh::lean_inc(v_val_719_);
        crate::leanh::lean_dec_ref_known(v_fst_717_, 1);
        v___x_720_ = (crate::leanh::lean_unbox(v_val_719_) as u8);
        crate::leanh::lean_dec(v_val_719_);
        return v___x_720_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg___boxed(
    mut v_m_721_: *mut crate::leanh::LeanObject,
    mut v_p_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_723_: u8 = 0;
    let mut v_r_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Std_DHashMap_Raw_all___redArg(v_m_721_, v_p_722_);
    v_r_724_ = crate::leanh::lean_box((v_res_723_) as usize);
    return v_r_724_;
}
pub unsafe fn l_Std_DHashMap_Raw_all(
    mut v_00_u03b1_725_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_726_: *mut crate::leanh::LeanObject,
    mut v_m_727_: *mut crate::leanh::LeanObject,
    mut v_p_728_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_735_: usize = 0;
    let mut v___x_736_: usize = 0;
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_730_ = crate::leanh::lean_ctor_get(v_m_727_, 1);
    crate::leanh::lean_inc_ref(v_buckets_730_);
    crate::leanh::lean_dec_ref(v_m_727_);
    v___x_731_ = crate::leanh::lean_box(0);
    v___x_732_ = l_Std_DHashMap_Raw_all___redArg___closed__0;
    v___f_733_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_733_, 0, v_p_728_);
    crate::leanh::lean_closure_set(v___f_733_, 1, v___x_731_);
    crate::leanh::lean_closure_set(v___f_733_, 2, v___x_732_);
    v___f_734_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_734_, 0, v___x_729_);
    crate::leanh::lean_closure_set(v___f_734_, 1, v___f_733_);
    v_sz_735_ = lean_array_size(v_buckets_730_);
    v___x_736_ = 0usize;
    v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_729_,
        v_buckets_730_,
        v___f_734_,
        v_sz_735_,
        v___x_736_,
        v___x_732_,
    );
    v_fst_738_ = crate::leanh::lean_ctor_get(v___x_737_, 0);
    crate::leanh::lean_inc(v_fst_738_);
    crate::leanh::lean_dec(v___x_737_);
    if crate::leanh::lean_obj_tag(v_fst_738_) == 0 {
        let mut v___x_739_: u8 = 0;
        v___x_739_ = 1;
        return v___x_739_;
    } else {
        let mut v_val_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_741_: u8 = 0;
        v_val_740_ = crate::leanh::lean_ctor_get(v_fst_738_, 0);
        crate::leanh::lean_inc(v_val_740_);
        crate::leanh::lean_dec_ref_known(v_fst_738_, 1);
        v___x_741_ = (crate::leanh::lean_unbox(v_val_740_) as u8);
        crate::leanh::lean_dec(v_val_740_);
        return v___x_741_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_all___boxed(
    mut v_00_u03b1_742_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_743_: *mut crate::leanh::LeanObject,
    mut v_m_744_: *mut crate::leanh::LeanObject,
    mut v_p_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_746_: u8 = 0;
    let mut v_r_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Std_DHashMap_Raw_all(v_00_u03b1_742_, v_00_u03b2_743_, v_m_744_, v_p_745_);
    v_r_747_ = crate::leanh::lean_box((v_res_746_) as usize);
    return v_r_747_;
}
pub unsafe fn l_Std_DHashMap_Raw_any___redArg___lam__0(
    mut v_p_748_: *mut crate::leanh::LeanObject,
    mut v___x_749_: *mut crate::leanh::LeanObject,
    mut v___x_750_: *mut crate::leanh::LeanObject,
    mut v_a_751_: *mut crate::leanh::LeanObject,
    mut v_b_752_: *mut crate::leanh::LeanObject,
    mut v_acc_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: u8 = 0;
    v___x_754_ = crate::leanh::lean_apply_2(v_p_748_, v_a_751_, v_b_752_);
    v___x_755_ = (crate::leanh::lean_unbox(v___x_754_) as u8);
    if v___x_755_ == 0 {
        let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_756_, 0, v___x_749_);
        return v___x_756_;
    } else {
        let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_749_);
        v___x_757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_754_);
        v___x_758_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_758_, 0, v___x_757_);
        crate::leanh::lean_ctor_set(v___x_758_, 1, v___x_750_);
        v___x_759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_759_, 0, v___x_758_);
        return v___x_759_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_any___redArg___lam__0___boxed(
    mut v_p_760_: *mut crate::leanh::LeanObject,
    mut v___x_761_: *mut crate::leanh::LeanObject,
    mut v___x_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
    mut v_b_764_: *mut crate::leanh::LeanObject,
    mut v_acc_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Std_DHashMap_Raw_any___redArg___lam__0(
        v_p_760_, v___x_761_, v___x_762_, v_a_763_, v_b_764_, v_acc_765_,
    );
    crate::leanh::lean_dec_ref(v_acc_765_);
    return v_res_766_;
}
pub unsafe fn l_Std_DHashMap_Raw_any___redArg(
    mut v_m_767_: *mut crate::leanh::LeanObject,
    mut v_p_768_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_775_: usize = 0;
    let mut v___x_776_: usize = 0;
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_769_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_770_ = crate::leanh::lean_ctor_get(v_m_767_, 1);
    crate::leanh::lean_inc_ref(v_buckets_770_);
    crate::leanh::lean_dec_ref(v_m_767_);
    v___x_771_ = crate::leanh::lean_box(0);
    v___x_772_ = l_Std_DHashMap_Raw_all___redArg___closed__0;
    v___f_773_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_773_, 0, v_p_768_);
    crate::leanh::lean_closure_set(v___f_773_, 1, v___x_772_);
    crate::leanh::lean_closure_set(v___f_773_, 2, v___x_771_);
    v___f_774_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_774_, 0, v___x_769_);
    crate::leanh::lean_closure_set(v___f_774_, 1, v___f_773_);
    v_sz_775_ = lean_array_size(v_buckets_770_);
    v___x_776_ = 0usize;
    v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_769_,
        v_buckets_770_,
        v___f_774_,
        v_sz_775_,
        v___x_776_,
        v___x_772_,
    );
    v_fst_778_ = crate::leanh::lean_ctor_get(v___x_777_, 0);
    crate::leanh::lean_inc(v_fst_778_);
    crate::leanh::lean_dec(v___x_777_);
    if crate::leanh::lean_obj_tag(v_fst_778_) == 0 {
        let mut v___x_779_: u8 = 0;
        v___x_779_ = 0;
        return v___x_779_;
    } else {
        let mut v_val_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_781_: u8 = 0;
        v_val_780_ = crate::leanh::lean_ctor_get(v_fst_778_, 0);
        crate::leanh::lean_inc(v_val_780_);
        crate::leanh::lean_dec_ref_known(v_fst_778_, 1);
        v___x_781_ = (crate::leanh::lean_unbox(v_val_780_) as u8);
        crate::leanh::lean_dec(v_val_780_);
        return v___x_781_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_any___redArg___boxed(
    mut v_m_782_: *mut crate::leanh::LeanObject,
    mut v_p_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_784_: u8 = 0;
    let mut v_r_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Std_DHashMap_Raw_any___redArg(v_m_782_, v_p_783_);
    v_r_785_ = crate::leanh::lean_box((v_res_784_) as usize);
    return v_r_785_;
}
pub unsafe fn l_Std_DHashMap_Raw_any(
    mut v_00_u03b1_786_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_787_: *mut crate::leanh::LeanObject,
    mut v_m_788_: *mut crate::leanh::LeanObject,
    mut v_p_789_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_796_: usize = 0;
    let mut v___x_797_: usize = 0;
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_791_ = crate::leanh::lean_ctor_get(v_m_788_, 1);
    crate::leanh::lean_inc_ref(v_buckets_791_);
    crate::leanh::lean_dec_ref(v_m_788_);
    v___x_792_ = crate::leanh::lean_box(0);
    v___x_793_ = l_Std_DHashMap_Raw_all___redArg___closed__0;
    v___f_794_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_794_, 0, v_p_789_);
    crate::leanh::lean_closure_set(v___f_794_, 1, v___x_793_);
    crate::leanh::lean_closure_set(v___f_794_, 2, v___x_792_);
    v___f_795_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_795_, 0, v___x_790_);
    crate::leanh::lean_closure_set(v___f_795_, 1, v___f_794_);
    v_sz_796_ = lean_array_size(v_buckets_791_);
    v___x_797_ = 0usize;
    v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_790_,
        v_buckets_791_,
        v___f_795_,
        v_sz_796_,
        v___x_797_,
        v___x_793_,
    );
    v_fst_799_ = crate::leanh::lean_ctor_get(v___x_798_, 0);
    crate::leanh::lean_inc(v_fst_799_);
    crate::leanh::lean_dec(v___x_798_);
    if crate::leanh::lean_obj_tag(v_fst_799_) == 0 {
        let mut v___x_800_: u8 = 0;
        v___x_800_ = 0;
        return v___x_800_;
    } else {
        let mut v_val_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_802_: u8 = 0;
        v_val_801_ = crate::leanh::lean_ctor_get(v_fst_799_, 0);
        crate::leanh::lean_inc(v_val_801_);
        crate::leanh::lean_dec_ref_known(v_fst_799_, 1);
        v___x_802_ = (crate::leanh::lean_unbox(v_val_801_) as u8);
        crate::leanh::lean_dec(v_val_801_);
        return v___x_802_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_any___boxed(
    mut v_00_u03b1_803_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_804_: *mut crate::leanh::LeanObject,
    mut v_m_805_: *mut crate::leanh::LeanObject,
    mut v_p_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_807_: u8 = 0;
    let mut v_r_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_807_ = l_Std_DHashMap_Raw_any(v_00_u03b1_803_, v_00_u03b2_804_, v_m_805_, v_p_806_);
    v_r_808_ = crate::leanh::lean_box((v_res_807_) as usize);
    return v_r_808_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_RawDef(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_RawDef(
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
pub unsafe fn initialize_Std_Data_DHashMap_RawDef(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_RawDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_RawDef(builtin);
}
