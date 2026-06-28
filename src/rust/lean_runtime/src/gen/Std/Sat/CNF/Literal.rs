// Lean compiler output
// Module: Std.Sat.CNF.Literal
// Imports: Init.Data.Hashable Init.Data.ToString
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_unbox,
};
pub unsafe fn l_Std_Sat_Literal_negate___redArg(mut v_l_52_: *mut LeanObject) -> *mut LeanObject {
    let mut v_snd_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_54_: u8 = 0;
    let mut v_fst_55_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_58_: u8 = 0;
    let mut v___x_59_: u8 = 0;
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_63_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_64_: u8 = 0;
    let mut v_unused_65_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_66_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_69_: u8 = 0;
    let mut v___x_70_: u8 = 0;
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_74_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_75_: u8 = 0;
    let mut v_unused_76_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_53_ = lean_ctor_get(v_l_52_, 1);
                v___x_54_ = (lean_unbox(v_snd_53_) as u8);
                if v___x_54_ == 0 {
                    v_fst_55_ = lean_ctor_get(v_l_52_, 0);
                    v_isSharedCheck_64_ = (!lean_is_exclusive(v_l_52_)) as u8;
                    if v_isSharedCheck_64_ == 0 {
                        v_unused_65_ = lean_ctor_get(v_l_52_, 1);
                        lean_dec(v_unused_65_);
                        v___x_57_ = v_l_52_;
                        v_isShared_58_ = v_isSharedCheck_64_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_55_);
                        lean_dec(v_l_52_);
                        v___x_57_ = lean_box(0);
                        v_isShared_58_ = v_isSharedCheck_64_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_66_ = lean_ctor_get(v_l_52_, 0);
                    v_isSharedCheck_75_ = (!lean_is_exclusive(v_l_52_)) as u8;
                    if v_isSharedCheck_75_ == 0 {
                        v_unused_76_ = lean_ctor_get(v_l_52_, 1);
                        lean_dec(v_unused_76_);
                        v___x_68_ = v_l_52_;
                        v_isShared_69_ = v_isSharedCheck_75_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_fst_66_);
                        lean_dec(v_l_52_);
                        v___x_68_ = lean_box(0);
                        v_isShared_69_ = v_isSharedCheck_75_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_59_ = 1;
                v___x_60_ = lean_box((v___x_59_) as usize);
                if v_isShared_58_ == 0 {
                    lean_ctor_set(v___x_57_, 1, v___x_60_);
                    v___x_62_ = v___x_57_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_63_, 0, v_fst_55_);
                    lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_60_);
                    v___x_62_ = v_reuseFailAlloc_63_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_62_;
            }
            3 => {
                v___x_70_ = 0;
                v___x_71_ = lean_box((v___x_70_) as usize);
                if v_isShared_69_ == 0 {
                    lean_ctor_set(v___x_68_, 1, v___x_71_);
                    v___x_73_ = v___x_68_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_74_, 0, v_fst_66_);
                    lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_71_);
                    v___x_73_ = v_reuseFailAlloc_74_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_73_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_Literal_negate(
    mut v_00_u03b1_77_: *mut LeanObject,
    mut v_l_78_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_79_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_80_: u8 = 0;
    let mut v_fst_81_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_84_: u8 = 0;
    let mut v___x_85_: u8 = 0;
    let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_89_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_90_: u8 = 0;
    let mut v_unused_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_92_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_95_: u8 = 0;
    let mut v___x_96_: u8 = 0;
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_101_: u8 = 0;
    let mut v_unused_102_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_79_ = lean_ctor_get(v_l_78_, 1);
                v___x_80_ = (lean_unbox(v_snd_79_) as u8);
                if v___x_80_ == 0 {
                    v_fst_81_ = lean_ctor_get(v_l_78_, 0);
                    v_isSharedCheck_90_ = (!lean_is_exclusive(v_l_78_)) as u8;
                    if v_isSharedCheck_90_ == 0 {
                        v_unused_91_ = lean_ctor_get(v_l_78_, 1);
                        lean_dec(v_unused_91_);
                        v___x_83_ = v_l_78_;
                        v_isShared_84_ = v_isSharedCheck_90_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_81_);
                        lean_dec(v_l_78_);
                        v___x_83_ = lean_box(0);
                        v_isShared_84_ = v_isSharedCheck_90_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_92_ = lean_ctor_get(v_l_78_, 0);
                    v_isSharedCheck_101_ = (!lean_is_exclusive(v_l_78_)) as u8;
                    if v_isSharedCheck_101_ == 0 {
                        v_unused_102_ = lean_ctor_get(v_l_78_, 1);
                        lean_dec(v_unused_102_);
                        v___x_94_ = v_l_78_;
                        v_isShared_95_ = v_isSharedCheck_101_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_fst_92_);
                        lean_dec(v_l_78_);
                        v___x_94_ = lean_box(0);
                        v_isShared_95_ = v_isSharedCheck_101_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_85_ = 1;
                v___x_86_ = lean_box((v___x_85_) as usize);
                if v_isShared_84_ == 0 {
                    lean_ctor_set(v___x_83_, 1, v___x_86_);
                    v___x_88_ = v___x_83_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_89_, 0, v_fst_81_);
                    lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_86_);
                    v___x_88_ = v_reuseFailAlloc_89_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_88_;
            }
            3 => {
                v___x_96_ = 0;
                v___x_97_ = lean_box((v___x_96_) as usize);
                if v_isShared_95_ == 0 {
                    lean_ctor_set(v___x_94_, 1, v___x_97_);
                    v___x_99_ = v___x_94_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_100_, 0, v_fst_92_);
                    lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_97_);
                    v___x_99_ = v_reuseFailAlloc_100_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_99_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_CNF_Literal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_CNF_Literal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_CNF_Literal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Literal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_CNF_Literal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_CNF_Literal(builtin);
}
