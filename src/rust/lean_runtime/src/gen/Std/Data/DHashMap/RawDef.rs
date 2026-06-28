// Lean compiler output
// Module: Std.Data.DHashMap.RawDef
// Imports: Std.Data.DHashMap.Internal.AssocList.Basic Init.Data.Array.Basic
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_dec_le, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_DHashMap_Raw_fold___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Std_DHashMap_Raw_fold___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_fold___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_fold___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_fold___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_fold___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_fold___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_DHashMap_Raw_all___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Std_DHashMap_Raw_all___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_all___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_DHashMap_Raw_foldM___redArg___lam__0(
    mut v_inst_405_: *mut LeanObject,
    mut v_f_406_: *mut LeanObject,
    mut v_acc_407_: *mut LeanObject,
    mut v_l_408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    v___x_409_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_405_,
        v_f_406_,
        v_acc_407_,
        v_l_408_,
    );
    return v___x_409_;
}
pub unsafe fn l_Std_DHashMap_Raw_foldM___redArg(
    mut v_inst_410_: *mut LeanObject,
    mut v_f_411_: *mut LeanObject,
    mut v_init_412_: *mut LeanObject,
    mut v_b_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: u8 = 0;
    v_buckets_414_ = lean_ctor_get(v_b_413_, 1);
    lean_inc_ref(v_buckets_414_);
    lean_dec_ref(v_b_413_);
    v___x_415_ = lean_unsigned_to_nat(0);
    v___x_416_ = lean_array_get_size(v_buckets_414_);
    v___x_417_ = lean_nat_dec_lt(v___x_415_, v___x_416_);
    if v___x_417_ == 0 {
        let mut v_toApplicative_418_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_414_);
        lean_dec(v_f_411_);
        v_toApplicative_418_ = lean_ctor_get(v_inst_410_, 0);
        lean_inc_ref(v_toApplicative_418_);
        lean_dec_ref(v_inst_410_);
        v_toPure_419_ = lean_ctor_get(v_toApplicative_418_, 1);
        lean_inc(v_toPure_419_);
        lean_dec_ref(v_toApplicative_418_);
        v___x_420_ = lean_apply_2(v_toPure_419_, lean_box(0), v_init_412_);
        return v___x_420_;
    } else {
        let mut v___f_421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_422_: u8 = 0;
        lean_inc_ref(v_inst_410_);
        v___f_421_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_421_, 0, v_inst_410_);
        lean_closure_set(v___f_421_, 1, v_f_411_);
        v___x_422_ = lean_nat_dec_le(v___x_416_, v___x_416_);
        if v___x_422_ == 0 {
            if v___x_417_ == 0 {
                let mut v_toApplicative_423_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_424_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_421_);
                lean_dec_ref(v_buckets_414_);
                v_toApplicative_423_ = lean_ctor_get(v_inst_410_, 0);
                lean_inc_ref(v_toApplicative_423_);
                lean_dec_ref(v_inst_410_);
                v_toPure_424_ = lean_ctor_get(v_toApplicative_423_, 1);
                lean_inc(v_toPure_424_);
                lean_dec_ref(v_toApplicative_423_);
                v___x_425_ = lean_apply_2(v_toPure_424_, lean_box(0), v_init_412_);
                return v___x_425_;
            } else {
                let mut v___x_426_: usize = 0;
                let mut v___x_427_: usize = 0;
                let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
                v___x_426_ = 0usize;
                v___x_427_ = lean_usize_of_nat(v___x_416_);
                v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
            v___x_429_ = 0usize;
            v___x_430_ = lean_usize_of_nat(v___x_416_);
            v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_432_: *mut LeanObject,
    mut v_00_u03b2_433_: *mut LeanObject,
    mut v_00_u03b4_434_: *mut LeanObject,
    mut v_m_435_: *mut LeanObject,
    mut v_inst_436_: *mut LeanObject,
    mut v_f_437_: *mut LeanObject,
    mut v_init_438_: *mut LeanObject,
    mut v_b_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    v_buckets_440_ = lean_ctor_get(v_b_439_, 1);
    lean_inc_ref(v_buckets_440_);
    lean_dec_ref(v_b_439_);
    v___x_441_ = lean_unsigned_to_nat(0);
    v___x_442_ = lean_array_get_size(v_buckets_440_);
    v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
    if v___x_443_ == 0 {
        let mut v_toApplicative_444_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_440_);
        lean_dec(v_f_437_);
        v_toApplicative_444_ = lean_ctor_get(v_inst_436_, 0);
        lean_inc_ref(v_toApplicative_444_);
        lean_dec_ref(v_inst_436_);
        v_toPure_445_ = lean_ctor_get(v_toApplicative_444_, 1);
        lean_inc(v_toPure_445_);
        lean_dec_ref(v_toApplicative_444_);
        v___x_446_ = lean_apply_2(v_toPure_445_, lean_box(0), v_init_438_);
        return v___x_446_;
    } else {
        let mut v___f_447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_448_: u8 = 0;
        lean_inc_ref(v_inst_436_);
        v___f_447_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_447_, 0, v_inst_436_);
        lean_closure_set(v___f_447_, 1, v_f_437_);
        v___x_448_ = lean_nat_dec_le(v___x_442_, v___x_442_);
        if v___x_448_ == 0 {
            if v___x_443_ == 0 {
                let mut v_toApplicative_449_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_450_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_447_);
                lean_dec_ref(v_buckets_440_);
                v_toApplicative_449_ = lean_ctor_get(v_inst_436_, 0);
                lean_inc_ref(v_toApplicative_449_);
                lean_dec_ref(v_inst_436_);
                v_toPure_450_ = lean_ctor_get(v_toApplicative_449_, 1);
                lean_inc(v_toPure_450_);
                lean_dec_ref(v_toApplicative_449_);
                v___x_451_ = lean_apply_2(v_toPure_450_, lean_box(0), v_init_438_);
                return v___x_451_;
            } else {
                let mut v___x_452_: usize = 0;
                let mut v___x_453_: usize = 0;
                let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
                v___x_452_ = 0usize;
                v___x_453_ = lean_usize_of_nat(v___x_442_);
                v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
            v___x_455_ = 0usize;
            v___x_456_ = lean_usize_of_nat(v___x_442_);
            v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_f_458_: *mut LeanObject,
    mut v_x1_459_: *mut LeanObject,
    mut v_x2_460_: *mut LeanObject,
    mut v_x3_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    v___x_462_ = lean_apply_3(v_f_458_, v_x1_459_, v_x2_460_, v_x3_461_);
    return v___x_462_;
}
pub unsafe fn l_Std_DHashMap_Raw_fold___redArg___lam__1(
    mut v___x_463_: *mut LeanObject,
    mut v___f_464_: *mut LeanObject,
    mut v_acc_465_: *mut LeanObject,
    mut v_l_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_463_, v___f_464_, v_acc_465_, v_l_466_,
    );
    return v___x_467_;
}
pub unsafe fn l_Std_DHashMap_Raw_fold___redArg(
    mut v_f_487_: *mut LeanObject,
    mut v_init_488_: *mut LeanObject,
    mut v_b_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    v___x_490_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_491_ = lean_ctor_get(v_b_489_, 1);
    lean_inc_ref(v_buckets_491_);
    lean_dec_ref(v_b_489_);
    v___x_492_ = lean_unsigned_to_nat(0);
    v___x_493_ = lean_array_get_size(v_buckets_491_);
    v___x_494_ = lean_nat_dec_lt(v___x_492_, v___x_493_);
    if v___x_494_ == 0 {
        lean_dec_ref(v_buckets_491_);
        lean_dec(v_f_487_);
        return v_init_488_;
    } else {
        let mut v___f_495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_497_: u8 = 0;
        v___f_495_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_495_, 0, v_f_487_);
        v___f_496_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_496_, 0, v___x_490_);
        lean_closure_set(v___f_496_, 1, v___f_495_);
        v___x_497_ = lean_nat_dec_le(v___x_493_, v___x_493_);
        if v___x_497_ == 0 {
            if v___x_494_ == 0 {
                lean_dec_ref(v___f_496_);
                lean_dec_ref(v_buckets_491_);
                return v_init_488_;
            } else {
                let mut v___x_498_: usize = 0;
                let mut v___x_499_: usize = 0;
                let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
                v___x_498_ = 0usize;
                v___x_499_ = lean_usize_of_nat(v___x_493_);
                v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
            v___x_501_ = 0usize;
            v___x_502_ = lean_usize_of_nat(v___x_493_);
            v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_504_: *mut LeanObject,
    mut v_00_u03b2_505_: *mut LeanObject,
    mut v_00_u03b4_506_: *mut LeanObject,
    mut v_f_507_: *mut LeanObject,
    mut v_init_508_: *mut LeanObject,
    mut v_b_509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: u8 = 0;
    v___x_510_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_511_ = lean_ctor_get(v_b_509_, 1);
    lean_inc_ref(v_buckets_511_);
    lean_dec_ref(v_b_509_);
    v___x_512_ = lean_unsigned_to_nat(0);
    v___x_513_ = lean_array_get_size(v_buckets_511_);
    v___x_514_ = lean_nat_dec_lt(v___x_512_, v___x_513_);
    if v___x_514_ == 0 {
        lean_dec_ref(v_buckets_511_);
        lean_dec(v_f_507_);
        return v_init_508_;
    } else {
        let mut v___f_515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_517_: u8 = 0;
        v___f_515_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_515_, 0, v_f_507_);
        v___f_516_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_516_, 0, v___x_510_);
        lean_closure_set(v___f_516_, 1, v___f_515_);
        v___x_517_ = lean_nat_dec_le(v___x_513_, v___x_513_);
        if v___x_517_ == 0 {
            if v___x_514_ == 0 {
                lean_dec_ref(v___f_516_);
                lean_dec_ref(v_buckets_511_);
                return v_init_508_;
            } else {
                let mut v___x_518_: usize = 0;
                let mut v___x_519_: usize = 0;
                let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
                v___x_518_ = 0usize;
                v___x_519_ = lean_usize_of_nat(v___x_513_);
                v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
            v___x_521_ = 0usize;
            v___x_522_ = lean_usize_of_nat(v___x_513_);
            v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_f_524_: *mut LeanObject,
    mut v_x_525_: *mut LeanObject,
    mut v___y_526_: *mut LeanObject,
    mut v___y_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    v___x_528_ = lean_apply_2(v_f_524_, v___y_526_, v___y_527_);
    return v___x_528_;
}
pub unsafe fn l_Std_DHashMap_Raw_forM___redArg___lam__1(
    mut v_inst_529_: *mut LeanObject,
    mut v___f_530_: *mut LeanObject,
    mut v_x_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    v___x_533_ = lean_box(0);
    v___x_534_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_529_,
        v___f_530_,
        v___x_533_,
        v___y_532_,
    );
    return v___x_534_;
}
pub unsafe fn l_Std_DHashMap_Raw_forM___redArg(
    mut v_inst_535_: *mut LeanObject,
    mut v_f_536_: *mut LeanObject,
    mut v_b_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: u8 = 0;
    v_buckets_538_ = lean_ctor_get(v_b_537_, 1);
    lean_inc_ref(v_buckets_538_);
    lean_dec_ref(v_b_537_);
    v___x_539_ = lean_unsigned_to_nat(0);
    v___x_540_ = lean_array_get_size(v_buckets_538_);
    v___x_541_ = lean_box(0);
    v___x_542_ = lean_nat_dec_lt(v___x_539_, v___x_540_);
    if v___x_542_ == 0 {
        let mut v_toApplicative_543_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_538_);
        lean_dec(v_f_536_);
        v_toApplicative_543_ = lean_ctor_get(v_inst_535_, 0);
        lean_inc_ref(v_toApplicative_543_);
        lean_dec_ref(v_inst_535_);
        v_toPure_544_ = lean_ctor_get(v_toApplicative_543_, 1);
        lean_inc(v_toPure_544_);
        lean_dec_ref(v_toApplicative_543_);
        v___x_545_ = lean_apply_2(v_toPure_544_, lean_box(0), v___x_541_);
        return v___x_545_;
    } else {
        let mut v___f_546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_548_: u8 = 0;
        v___f_546_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_546_, 0, v_f_536_);
        lean_inc_ref(v_inst_535_);
        v___f_547_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_547_, 0, v_inst_535_);
        lean_closure_set(v___f_547_, 1, v___f_546_);
        v___x_548_ = lean_nat_dec_le(v___x_540_, v___x_540_);
        if v___x_548_ == 0 {
            if v___x_542_ == 0 {
                let mut v_toApplicative_549_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_550_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_547_);
                lean_dec_ref(v_buckets_538_);
                v_toApplicative_549_ = lean_ctor_get(v_inst_535_, 0);
                lean_inc_ref(v_toApplicative_549_);
                lean_dec_ref(v_inst_535_);
                v_toPure_550_ = lean_ctor_get(v_toApplicative_549_, 1);
                lean_inc(v_toPure_550_);
                lean_dec_ref(v_toApplicative_549_);
                v___x_551_ = lean_apply_2(v_toPure_550_, lean_box(0), v___x_541_);
                return v___x_551_;
            } else {
                let mut v___x_552_: usize = 0;
                let mut v___x_553_: usize = 0;
                let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
                v___x_552_ = 0usize;
                v___x_553_ = lean_usize_of_nat(v___x_540_);
                v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
            v___x_555_ = 0usize;
            v___x_556_ = lean_usize_of_nat(v___x_540_);
            v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_558_: *mut LeanObject,
    mut v_00_u03b2_559_: *mut LeanObject,
    mut v_m_560_: *mut LeanObject,
    mut v_inst_561_: *mut LeanObject,
    mut v_f_562_: *mut LeanObject,
    mut v_b_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: u8 = 0;
    v_buckets_564_ = lean_ctor_get(v_b_563_, 1);
    lean_inc_ref(v_buckets_564_);
    lean_dec_ref(v_b_563_);
    v___x_565_ = lean_unsigned_to_nat(0);
    v___x_566_ = lean_array_get_size(v_buckets_564_);
    v___x_567_ = lean_box(0);
    v___x_568_ = lean_nat_dec_lt(v___x_565_, v___x_566_);
    if v___x_568_ == 0 {
        let mut v_toApplicative_569_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_564_);
        lean_dec(v_f_562_);
        v_toApplicative_569_ = lean_ctor_get(v_inst_561_, 0);
        lean_inc_ref(v_toApplicative_569_);
        lean_dec_ref(v_inst_561_);
        v_toPure_570_ = lean_ctor_get(v_toApplicative_569_, 1);
        lean_inc(v_toPure_570_);
        lean_dec_ref(v_toApplicative_569_);
        v___x_571_ = lean_apply_2(v_toPure_570_, lean_box(0), v___x_567_);
        return v___x_571_;
    } else {
        let mut v___f_572_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_574_: u8 = 0;
        v___f_572_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_572_, 0, v_f_562_);
        lean_inc_ref(v_inst_561_);
        v___f_573_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_573_, 0, v_inst_561_);
        lean_closure_set(v___f_573_, 1, v___f_572_);
        v___x_574_ = lean_nat_dec_le(v___x_566_, v___x_566_);
        if v___x_574_ == 0 {
            if v___x_568_ == 0 {
                let mut v_toApplicative_575_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_576_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_573_);
                lean_dec_ref(v_buckets_564_);
                v_toApplicative_575_ = lean_ctor_get(v_inst_561_, 0);
                lean_inc_ref(v_toApplicative_575_);
                lean_dec_ref(v_inst_561_);
                v_toPure_576_ = lean_ctor_get(v_toApplicative_575_, 1);
                lean_inc(v_toPure_576_);
                lean_dec_ref(v_toApplicative_575_);
                v___x_577_ = lean_apply_2(v_toPure_576_, lean_box(0), v___x_567_);
                return v___x_577_;
            } else {
                let mut v___x_578_: usize = 0;
                let mut v___x_579_: usize = 0;
                let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
                v___x_578_ = 0usize;
                v___x_579_ = lean_usize_of_nat(v___x_566_);
                v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
            v___x_581_ = 0usize;
            v___x_582_ = lean_usize_of_nat(v___x_566_);
            v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_inst_584_: *mut LeanObject,
    mut v_f_585_: *mut LeanObject,
    mut v_a_586_: *mut LeanObject,
    mut v_x_587_: *mut LeanObject,
    mut v___y_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    v___x_589_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_584_, v_f_585_, v_a_586_, v___y_588_);
    return v___x_589_;
}
pub unsafe fn l_Std_DHashMap_Raw_forIn___redArg(
    mut v_inst_590_: *mut LeanObject,
    mut v_f_591_: *mut LeanObject,
    mut v_init_592_: *mut LeanObject,
    mut v_b_593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_596_: usize = 0;
    let mut v___x_597_: usize = 0;
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_594_ = lean_ctor_get(v_b_593_, 1);
    lean_inc_ref(v_buckets_594_);
    lean_dec_ref(v_b_593_);
    lean_inc_ref(v_inst_590_);
    v___f_595_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_595_, 0, v_inst_590_);
    lean_closure_set(v___f_595_, 1, v_f_591_);
    v_sz_596_ = lean_array_size(v_buckets_594_);
    v___x_597_ = 0usize;
    v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_00_u03b1_599_: *mut LeanObject,
    mut v_00_u03b2_600_: *mut LeanObject,
    mut v_00_u03b4_601_: *mut LeanObject,
    mut v_m_602_: *mut LeanObject,
    mut v_inst_603_: *mut LeanObject,
    mut v_f_604_: *mut LeanObject,
    mut v_init_605_: *mut LeanObject,
    mut v_b_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_609_: usize = 0;
    let mut v___x_610_: usize = 0;
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_607_ = lean_ctor_get(v_b_606_, 1);
    lean_inc_ref(v_buckets_607_);
    lean_dec_ref(v_b_606_);
    lean_inc_ref(v_inst_603_);
    v___f_608_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_608_, 0, v_inst_603_);
    lean_closure_set(v___f_608_, 1, v_f_604_);
    v_sz_609_ = lean_array_size(v_buckets_607_);
    v___x_610_ = 0usize;
    v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_f_612_: *mut LeanObject,
    mut v_x_613_: *mut LeanObject,
    mut v___y_614_: *mut LeanObject,
    mut v___y_615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v___x_616_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_616_, 0, v___y_614_);
    lean_ctor_set(v___x_616_, 1, v___y_615_);
    v___x_617_ = lean_apply_1(v_f_612_, v___x_616_);
    return v___x_617_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2(
    mut v_inst_618_: *mut LeanObject,
    mut v_m_619_: *mut LeanObject,
    mut v_f_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    v_buckets_621_ = lean_ctor_get(v_m_619_, 1);
    lean_inc_ref(v_buckets_621_);
    lean_dec_ref(v_m_619_);
    v___x_622_ = lean_unsigned_to_nat(0);
    v___x_623_ = lean_array_get_size(v_buckets_621_);
    v___x_624_ = lean_box(0);
    v___x_625_ = lean_nat_dec_lt(v___x_622_, v___x_623_);
    if v___x_625_ == 0 {
        let mut v_toApplicative_626_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_621_);
        lean_dec(v_f_620_);
        v_toApplicative_626_ = lean_ctor_get(v_inst_618_, 0);
        lean_inc_ref(v_toApplicative_626_);
        lean_dec_ref(v_inst_618_);
        v_toPure_627_ = lean_ctor_get(v_toApplicative_626_, 1);
        lean_inc(v_toPure_627_);
        lean_dec_ref(v_toApplicative_626_);
        v___x_628_ = lean_apply_2(v_toPure_627_, lean_box(0), v___x_624_);
        return v___x_628_;
    } else {
        let mut v___f_629_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_631_: u8 = 0;
        v___f_629_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_629_, 0, v_f_620_);
        lean_inc_ref(v_inst_618_);
        v___f_630_ = lean_alloc_closure(
            l_Std_DHashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_630_, 0, v_inst_618_);
        lean_closure_set(v___f_630_, 1, v___f_629_);
        v___x_631_ = lean_nat_dec_le(v___x_623_, v___x_623_);
        if v___x_631_ == 0 {
            if v___x_625_ == 0 {
                let mut v_toApplicative_632_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_633_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_630_);
                lean_dec_ref(v_buckets_621_);
                v_toApplicative_632_ = lean_ctor_get(v_inst_618_, 0);
                lean_inc_ref(v_toApplicative_632_);
                lean_dec_ref(v_inst_618_);
                v_toPure_633_ = lean_ctor_get(v_toApplicative_632_, 1);
                lean_inc(v_toPure_633_);
                lean_dec_ref(v_toApplicative_632_);
                v___x_634_ = lean_apply_2(v_toPure_633_, lean_box(0), v___x_624_);
                return v___x_634_;
            } else {
                let mut v___x_635_: usize = 0;
                let mut v___x_636_: usize = 0;
                let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
                v___x_635_ = 0usize;
                v___x_636_ = lean_usize_of_nat(v___x_623_);
                v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
            v___x_638_ = 0usize;
            v___x_639_ = lean_usize_of_nat(v___x_623_);
            v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_inst_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_642_: *mut LeanObject = core::ptr::null_mut();
    v___f_642_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_642_, 0, v_inst_641_);
    return v___f_642_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForMSigmaOfMonad(
    mut v_00_u03b1_643_: *mut LeanObject,
    mut v_00_u03b2_644_: *mut LeanObject,
    mut v_m_645_: *mut LeanObject,
    mut v_inst_646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_647_: *mut LeanObject = core::ptr::null_mut();
    v___f_647_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_647_, 0, v_inst_646_);
    return v___f_647_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0(
    mut v_f_648_: *mut LeanObject,
    mut v_a_649_: *mut LeanObject,
    mut v_b_650_: *mut LeanObject,
    mut v_acc_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    v___x_652_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_652_, 0, v_a_649_);
    lean_ctor_set(v___x_652_, 1, v_b_650_);
    v___x_653_ = lean_apply_2(v_f_648_, v___x_652_, v_acc_651_);
    return v___x_653_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(
    mut v_inst_654_: *mut LeanObject,
    mut v___f_655_: *mut LeanObject,
    mut v_a_656_: *mut LeanObject,
    mut v_x_657_: *mut LeanObject,
    mut v___y_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    v___x_659_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_654_, v___f_655_, v_a_656_, v___y_658_);
    return v___x_659_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(
    mut v_inst_660_: *mut LeanObject,
    mut v_00_u03b2_661_: *mut LeanObject,
    mut v_m_662_: *mut LeanObject,
    mut v_init_663_: *mut LeanObject,
    mut v_f_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_668_: usize = 0;
    let mut v___x_669_: usize = 0;
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_665_ = lean_ctor_get(v_m_662_, 1);
    lean_inc_ref(v_buckets_665_);
    lean_dec_ref(v_m_662_);
    v___f_666_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_666_, 0, v_f_664_);
    lean_inc_ref(v_inst_660_);
    v___f_667_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_667_, 0, v_inst_660_);
    lean_closure_set(v___f_667_, 1, v___f_666_);
    v_sz_668_ = lean_array_size(v_buckets_665_);
    v___x_669_ = 0usize;
    v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_inst_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_672_: *mut LeanObject = core::ptr::null_mut();
    v___f_672_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_672_, 0, v_inst_671_);
    return v___f_672_;
}
pub unsafe fn l_Std_DHashMap_Raw_instForInSigmaOfMonad(
    mut v_00_u03b1_673_: *mut LeanObject,
    mut v_00_u03b2_674_: *mut LeanObject,
    mut v_m_675_: *mut LeanObject,
    mut v_inst_676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_677_: *mut LeanObject = core::ptr::null_mut();
    v___f_677_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_677_, 0, v_inst_676_);
    return v___f_677_;
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg___lam__0(
    mut v_p_678_: *mut LeanObject,
    mut v___x_679_: *mut LeanObject,
    mut v___x_680_: *mut LeanObject,
    mut v_a_681_: *mut LeanObject,
    mut v_b_682_: *mut LeanObject,
    mut v_acc_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    v___x_684_ = lean_apply_2(v_p_678_, v_a_681_, v_b_682_);
    v___x_685_ = (lean_unbox(v___x_684_) as u8);
    if v___x_685_ == 0 {
        let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_680_);
        v___x_686_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_686_, 0, v___x_684_);
        v___x_687_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_687_, 0, v___x_686_);
        lean_ctor_set(v___x_687_, 1, v___x_679_);
        v___x_688_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_688_, 0, v___x_687_);
        return v___x_688_;
    } else {
        let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
        v___x_689_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_689_, 0, v___x_680_);
        return v___x_689_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg___lam__0___boxed(
    mut v_p_690_: *mut LeanObject,
    mut v___x_691_: *mut LeanObject,
    mut v___x_692_: *mut LeanObject,
    mut v_a_693_: *mut LeanObject,
    mut v_b_694_: *mut LeanObject,
    mut v_acc_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_696_: *mut LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Std_DHashMap_Raw_all___redArg___lam__0(
        v_p_690_, v___x_691_, v___x_692_, v_a_693_, v_b_694_, v_acc_695_,
    );
    lean_dec_ref(v_acc_695_);
    return v_res_696_;
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg___lam__1(
    mut v___x_697_: *mut LeanObject,
    mut v___f_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
    mut v_x_700_: *mut LeanObject,
    mut v___y_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    v___x_702_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_697_, v___f_698_, v_a_699_, v___y_701_);
    return v___x_702_;
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg(
    mut v_m_706_: *mut LeanObject,
    mut v_p_707_: *mut LeanObject,
) -> u8 {
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_714_: usize = 0;
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_717_: *mut LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_709_ = lean_ctor_get(v_m_706_, 1);
    lean_inc_ref(v_buckets_709_);
    lean_dec_ref(v_m_706_);
    v___x_710_ = lean_box(0);
    v___x_711_ = l_Std_DHashMap_Raw_all___redArg___closed__0;
    v___f_712_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_712_, 0, v_p_707_);
    lean_closure_set(v___f_712_, 1, v___x_710_);
    lean_closure_set(v___f_712_, 2, v___x_711_);
    v___f_713_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_713_, 0, v___x_708_);
    lean_closure_set(v___f_713_, 1, v___f_712_);
    v_sz_714_ = lean_array_size(v_buckets_709_);
    v___x_715_ = 0usize;
    v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_708_,
        v_buckets_709_,
        v___f_713_,
        v_sz_714_,
        v___x_715_,
        v___x_711_,
    );
    v_fst_717_ = lean_ctor_get(v___x_716_, 0);
    lean_inc(v_fst_717_);
    lean_dec(v___x_716_);
    if lean_obj_tag(v_fst_717_) == 0 {
        let mut v___x_718_: u8 = 0;
        v___x_718_ = 1;
        return v___x_718_;
    } else {
        let mut v_val_719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_720_: u8 = 0;
        v_val_719_ = lean_ctor_get(v_fst_717_, 0);
        lean_inc(v_val_719_);
        lean_dec_ref_known(v_fst_717_, 1);
        v___x_720_ = (lean_unbox(v_val_719_) as u8);
        lean_dec(v_val_719_);
        return v___x_720_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_all___redArg___boxed(
    mut v_m_721_: *mut LeanObject,
    mut v_p_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_723_: u8 = 0;
    let mut v_r_724_: *mut LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Std_DHashMap_Raw_all___redArg(v_m_721_, v_p_722_);
    v_r_724_ = lean_box((v_res_723_) as usize);
    return v_r_724_;
}
pub unsafe fn l_Std_DHashMap_Raw_all(
    mut v_00_u03b1_725_: *mut LeanObject,
    mut v_00_u03b2_726_: *mut LeanObject,
    mut v_m_727_: *mut LeanObject,
    mut v_p_728_: *mut LeanObject,
) -> u8 {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_735_: usize = 0;
    let mut v___x_736_: usize = 0;
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_738_: *mut LeanObject = core::ptr::null_mut();
    v___x_729_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_730_ = lean_ctor_get(v_m_727_, 1);
    lean_inc_ref(v_buckets_730_);
    lean_dec_ref(v_m_727_);
    v___x_731_ = lean_box(0);
    v___x_732_ = l_Std_DHashMap_Raw_all___redArg___closed__0;
    v___f_733_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_733_, 0, v_p_728_);
    lean_closure_set(v___f_733_, 1, v___x_731_);
    lean_closure_set(v___f_733_, 2, v___x_732_);
    v___f_734_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_734_, 0, v___x_729_);
    lean_closure_set(v___f_734_, 1, v___f_733_);
    v_sz_735_ = lean_array_size(v_buckets_730_);
    v___x_736_ = 0usize;
    v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_729_,
        v_buckets_730_,
        v___f_734_,
        v_sz_735_,
        v___x_736_,
        v___x_732_,
    );
    v_fst_738_ = lean_ctor_get(v___x_737_, 0);
    lean_inc(v_fst_738_);
    lean_dec(v___x_737_);
    if lean_obj_tag(v_fst_738_) == 0 {
        let mut v___x_739_: u8 = 0;
        v___x_739_ = 1;
        return v___x_739_;
    } else {
        let mut v_val_740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_741_: u8 = 0;
        v_val_740_ = lean_ctor_get(v_fst_738_, 0);
        lean_inc(v_val_740_);
        lean_dec_ref_known(v_fst_738_, 1);
        v___x_741_ = (lean_unbox(v_val_740_) as u8);
        lean_dec(v_val_740_);
        return v___x_741_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_all___boxed(
    mut v_00_u03b1_742_: *mut LeanObject,
    mut v_00_u03b2_743_: *mut LeanObject,
    mut v_m_744_: *mut LeanObject,
    mut v_p_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_746_: u8 = 0;
    let mut v_r_747_: *mut LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Std_DHashMap_Raw_all(v_00_u03b1_742_, v_00_u03b2_743_, v_m_744_, v_p_745_);
    v_r_747_ = lean_box((v_res_746_) as usize);
    return v_r_747_;
}
pub unsafe fn l_Std_DHashMap_Raw_any___redArg___lam__0(
    mut v_p_748_: *mut LeanObject,
    mut v___x_749_: *mut LeanObject,
    mut v___x_750_: *mut LeanObject,
    mut v_a_751_: *mut LeanObject,
    mut v_b_752_: *mut LeanObject,
    mut v_acc_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: u8 = 0;
    v___x_754_ = lean_apply_2(v_p_748_, v_a_751_, v_b_752_);
    v___x_755_ = (lean_unbox(v___x_754_) as u8);
    if v___x_755_ == 0 {
        let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
        v___x_756_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_756_, 0, v___x_749_);
        return v___x_756_;
    } else {
        let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_749_);
        v___x_757_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_757_, 0, v___x_754_);
        v___x_758_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_758_, 0, v___x_757_);
        lean_ctor_set(v___x_758_, 1, v___x_750_);
        v___x_759_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_759_, 0, v___x_758_);
        return v___x_759_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_any___redArg___lam__0___boxed(
    mut v_p_760_: *mut LeanObject,
    mut v___x_761_: *mut LeanObject,
    mut v___x_762_: *mut LeanObject,
    mut v_a_763_: *mut LeanObject,
    mut v_b_764_: *mut LeanObject,
    mut v_acc_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_766_: *mut LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Std_DHashMap_Raw_any___redArg___lam__0(
        v_p_760_, v___x_761_, v___x_762_, v_a_763_, v_b_764_, v_acc_765_,
    );
    lean_dec_ref(v_acc_765_);
    return v_res_766_;
}
pub unsafe fn l_Std_DHashMap_Raw_any___redArg(
    mut v_m_767_: *mut LeanObject,
    mut v_p_768_: *mut LeanObject,
) -> u8 {
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_775_: usize = 0;
    let mut v___x_776_: usize = 0;
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_778_: *mut LeanObject = core::ptr::null_mut();
    v___x_769_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_770_ = lean_ctor_get(v_m_767_, 1);
    lean_inc_ref(v_buckets_770_);
    lean_dec_ref(v_m_767_);
    v___x_771_ = lean_box(0);
    v___x_772_ = l_Std_DHashMap_Raw_all___redArg___closed__0;
    v___f_773_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_773_, 0, v_p_768_);
    lean_closure_set(v___f_773_, 1, v___x_772_);
    lean_closure_set(v___f_773_, 2, v___x_771_);
    v___f_774_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_774_, 0, v___x_769_);
    lean_closure_set(v___f_774_, 1, v___f_773_);
    v_sz_775_ = lean_array_size(v_buckets_770_);
    v___x_776_ = 0usize;
    v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_769_,
        v_buckets_770_,
        v___f_774_,
        v_sz_775_,
        v___x_776_,
        v___x_772_,
    );
    v_fst_778_ = lean_ctor_get(v___x_777_, 0);
    lean_inc(v_fst_778_);
    lean_dec(v___x_777_);
    if lean_obj_tag(v_fst_778_) == 0 {
        let mut v___x_779_: u8 = 0;
        v___x_779_ = 0;
        return v___x_779_;
    } else {
        let mut v_val_780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_781_: u8 = 0;
        v_val_780_ = lean_ctor_get(v_fst_778_, 0);
        lean_inc(v_val_780_);
        lean_dec_ref_known(v_fst_778_, 1);
        v___x_781_ = (lean_unbox(v_val_780_) as u8);
        lean_dec(v_val_780_);
        return v___x_781_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_any___redArg___boxed(
    mut v_m_782_: *mut LeanObject,
    mut v_p_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_784_: u8 = 0;
    let mut v_r_785_: *mut LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Std_DHashMap_Raw_any___redArg(v_m_782_, v_p_783_);
    v_r_785_ = lean_box((v_res_784_) as usize);
    return v_r_785_;
}
pub unsafe fn l_Std_DHashMap_Raw_any(
    mut v_00_u03b1_786_: *mut LeanObject,
    mut v_00_u03b2_787_: *mut LeanObject,
    mut v_m_788_: *mut LeanObject,
    mut v_p_789_: *mut LeanObject,
) -> u8 {
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_796_: usize = 0;
    let mut v___x_797_: usize = 0;
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_790_ = l_Std_DHashMap_Raw_fold___redArg___closed__9;
    v_buckets_791_ = lean_ctor_get(v_m_788_, 1);
    lean_inc_ref(v_buckets_791_);
    lean_dec_ref(v_m_788_);
    v___x_792_ = lean_box(0);
    v___x_793_ = l_Std_DHashMap_Raw_all___redArg___closed__0;
    v___f_794_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_794_, 0, v_p_789_);
    lean_closure_set(v___f_794_, 1, v___x_793_);
    lean_closure_set(v___f_794_, 2, v___x_792_);
    v___f_795_ = lean_alloc_closure(
        l_Std_DHashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_795_, 0, v___x_790_);
    lean_closure_set(v___f_795_, 1, v___f_794_);
    v_sz_796_ = lean_array_size(v_buckets_791_);
    v___x_797_ = 0usize;
    v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_790_,
        v_buckets_791_,
        v___f_795_,
        v_sz_796_,
        v___x_797_,
        v___x_793_,
    );
    v_fst_799_ = lean_ctor_get(v___x_798_, 0);
    lean_inc(v_fst_799_);
    lean_dec(v___x_798_);
    if lean_obj_tag(v_fst_799_) == 0 {
        let mut v___x_800_: u8 = 0;
        v___x_800_ = 0;
        return v___x_800_;
    } else {
        let mut v_val_801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_802_: u8 = 0;
        v_val_801_ = lean_ctor_get(v_fst_799_, 0);
        lean_inc(v_val_801_);
        lean_dec_ref_known(v_fst_799_, 1);
        v___x_802_ = (lean_unbox(v_val_801_) as u8);
        lean_dec(v_val_801_);
        return v___x_802_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_any___boxed(
    mut v_00_u03b1_803_: *mut LeanObject,
    mut v_00_u03b2_804_: *mut LeanObject,
    mut v_m_805_: *mut LeanObject,
    mut v_p_806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_807_: u8 = 0;
    let mut v_r_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_807_ = l_Std_DHashMap_Raw_any(v_00_u03b1_803_, v_00_u03b2_804_, v_m_805_, v_p_806_);
    v_r_808_ = lean_box((v_res_807_) as usize);
    return v_r_808_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_RawDef(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_RawDef(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_RawDef(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_RawDef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_RawDef(builtin);
}
