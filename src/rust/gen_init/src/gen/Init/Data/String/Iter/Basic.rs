// Lean compiler output
// Module: Init.Data.String.Iter.Basic
// Imports: Init.Data.Iterators.Combinators.FilterMap Init.Data.Iterators.Consumers.Collect
use crate::ffi::{lean_array_push, lean_array_to_list};
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::WFExtrinsicFix::l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg;
pub static l_Std_Iter_toStringList___redArg___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Std_Iter_toStringList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toStringList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Iter_toStringList___redArg___lam__0(
    mut v_inst_46_: *mut leanh::LeanObject,
    mut v_inst_47_: *mut leanh::LeanObject,
    mut v_it_48_: *mut leanh::LeanObject,
    mut v_acc_49_: *mut leanh::LeanObject,
    mut v_recur_50_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_51_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_51_ = leanh::lean_apply_1(v_inst_46_, v_it_48_);
    match leanh::lean_obj_tag(v_val_51_) {
        0 => {
            let mut v_it_52_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_53_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_54_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_56_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_52_ = leanh::lean_ctor_get(v_val_51_, 0);
            leanh::lean_inc(v_it_52_);
            v_out_53_ = leanh::lean_ctor_get(v_val_51_, 1);
            leanh::lean_inc(v_out_53_);
            leanh::lean_dec_ref_known(v_val_51_, 2);
            v___x_54_ = leanh::lean_apply_1(v_inst_47_, v_out_53_);
            v___x_55_ = lean_array_push(v_acc_49_, v___x_54_);
            v___x_56_ = leanh::lean_apply_3(
                v_recur_50_,
                v_it_52_,
                v___x_55_,
                leanh::lean_box(0),
            );
            return v___x_56_;
        }
        1 => {
            let mut v_it_57_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_inst_47_);
            v_it_57_ = leanh::lean_ctor_get(v_val_51_, 0);
            leanh::lean_inc(v_it_57_);
            leanh::lean_dec_ref_known(v_val_51_, 1);
            v___x_58_ = leanh::lean_apply_3(
                v_recur_50_,
                v_it_57_,
                v_acc_49_,
                leanh::lean_box(0),
            );
            return v___x_58_;
        }
        _ => {
            leanh::lean_dec_ref(v_recur_50_);
            leanh::lean_dec_ref(v_inst_47_);
            return v_acc_49_;
        }
    }
}
pub unsafe fn l_Std_Iter_toStringList___redArg(
    mut v_inst_61_: *mut leanh::LeanObject,
    mut v_inst_62_: *mut leanh::LeanObject,
    mut v_it_63_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_64_ = leanh::lean_alloc_closure(
        l_Std_Iter_toStringList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_64_, 0, v_inst_61_);
    leanh::lean_closure_set(v___f_64_, 1, v_inst_62_);
    v___x_65_ = l_Std_Iter_toStringList___redArg___closed__0;
    v___x_66_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_64_, v_it_63_, v___x_65_,
    );
    v___x_67_ = lean_array_to_list(v___x_66_);
    return v___x_67_;
}
pub unsafe fn l_Std_Iter_toStringList(
    mut v_00_u03b1_68_: *mut leanh::LeanObject,
    mut v_00_u03b2_69_: *mut leanh::LeanObject,
    mut v_inst_70_: *mut leanh::LeanObject,
    mut v_inst_71_: *mut leanh::LeanObject,
    mut v_it_72_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_73_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_73_ = leanh::lean_alloc_closure(
        l_Std_Iter_toStringList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_73_, 0, v_inst_70_);
    leanh::lean_closure_set(v___f_73_, 1, v_inst_71_);
    v___x_74_ = l_Std_Iter_toStringList___redArg___closed__0;
    v___x_75_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_73_, v_it_72_, v___x_74_,
    );
    v___x_76_ = lean_array_to_list(v___x_75_);
    return v___x_76_;
}
pub unsafe fn l_Std_Iter_toStringArray___redArg(
    mut v_inst_77_: *mut leanh::LeanObject,
    mut v_inst_78_: *mut leanh::LeanObject,
    mut v_it_79_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_80_ = leanh::lean_alloc_closure(
        l_Std_Iter_toStringList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_80_, 0, v_inst_77_);
    leanh::lean_closure_set(v___f_80_, 1, v_inst_78_);
    v___x_81_ = l_Std_Iter_toStringList___redArg___closed__0;
    v___x_82_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_80_, v_it_79_, v___x_81_,
    );
    return v___x_82_;
}
pub unsafe fn l_Std_Iter_toStringArray(
    mut v_00_u03b1_83_: *mut leanh::LeanObject,
    mut v_00_u03b2_84_: *mut leanh::LeanObject,
    mut v_inst_85_: *mut leanh::LeanObject,
    mut v_inst_86_: *mut leanh::LeanObject,
    mut v_it_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_88_ = leanh::lean_alloc_closure(
        l_Std_Iter_toStringList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_88_, 0, v_inst_85_);
    leanh::lean_closure_set(v___f_88_, 1, v_inst_86_);
    v___x_89_ = l_Std_Iter_toStringList___redArg___closed__0;
    v___x_90_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_88_, v_it_87_, v___x_89_,
    );
    return v___x_90_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Iter_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Iter_Basic(
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
pub unsafe fn initialize_Init_Data_String_Iter_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iter_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Iter_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Iter_Basic(builtin);
}