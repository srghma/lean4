// Lean compiler output
// Module: Init.Data.BitVec.Folds
// Imports: Init.Data.BitVec.Basic Init.Data.BitVec.Basic Init.Ext Init.Data.BitVec.Lemmas Init.Data.Fin.Iterate
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, l_BitVec_cons, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::Fin::Iterate::{
    initialize_Init_Data_Fin_Iterate, l_Fin_hIterate___redArg,
    runtime_initialize_Init_Data_Fin_Iterate,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
static mut l_BitVec_iunfoldr___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_BitVec_iunfoldr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_BitVec_iunfoldr___redArg___lam__0(
    mut v_f_41_: *mut leanh::LeanObject,
    mut v_i_42_: *mut leanh::LeanObject,
    mut v_q_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_45_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_48_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_51_: u8 = 0;
    let mut v___x_52_: u8 = 0;
    let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_57_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_44_ = leanh::lean_ctor_get(v_q_43_, 0);
                leanh::lean_inc(v_fst_44_);
                v_snd_45_ = leanh::lean_ctor_get(v_q_43_, 1);
                leanh::lean_inc(v_snd_45_);
                leanh::lean_dec_ref(v_q_43_);
                leanh::lean_inc(v_i_42_);
                v___x_46_ = leanh::lean_apply_2(v_f_41_, v_i_42_, v_fst_44_);
                v_fst_47_ = leanh::lean_ctor_get(v___x_46_, 0);
                v_snd_48_ = leanh::lean_ctor_get(v___x_46_, 1);
                v_isSharedCheck_57_ = (!leanh::lean_is_exclusive(v___x_46_)) as u8;
                if v_isSharedCheck_57_ == 0 {
                    v___x_50_ = v___x_46_;
                    v_isShared_51_ = v_isSharedCheck_57_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_48_);
                    leanh::lean_inc(v_fst_47_);
                    leanh::lean_dec(v___x_46_);
                    v___x_50_ = leanh::lean_box(0);
                    v_isShared_51_ = v_isSharedCheck_57_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_52_ = (leanh::lean_unbox(v_snd_48_) as u8);
                leanh::lean_dec(v_snd_48_);
                v___x_53_ = l_BitVec_cons(v_i_42_, v___x_52_, v_snd_45_);
                leanh::lean_dec(v_snd_45_);
                leanh::lean_dec(v_i_42_);
                if v_isShared_51_ == 0 {
                    leanh::lean_ctor_set(v___x_50_, 1, v___x_53_);
                    v___x_55_ = v___x_50_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_56_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_56_, 0, v_fst_47_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_53_);
                    v___x_55_ = v_reuseFailAlloc_56_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_55_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_BitVec_iunfoldr___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_58_ = leanh::lean_unsigned_to_nat(0);
    v___x_59_ = l_BitVec_ofNat(v___x_58_, v___x_58_);
    return v___x_59_;
}
pub unsafe fn l_BitVec_iunfoldr___redArg(
    mut v_w_60_: *mut leanh::LeanObject,
    mut v_f_61_: *mut leanh::LeanObject,
    mut v_s_62_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_63_ = leanh::lean_alloc_closure(
        l_BitVec_iunfoldr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_63_, 0, v_f_61_);
    v___x_64_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_BitVec_iunfoldr___redArg___closed__0),
        core::ptr::addr_of_mut!(l_BitVec_iunfoldr___redArg___closed__0_once),
        _init_l_BitVec_iunfoldr___redArg___closed__0,
    );
    v___x_65_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_65_, 0, v_s_62_);
    leanh::lean_ctor_set(v___x_65_, 1, v___x_64_);
    v___x_66_ = l_Fin_hIterate___redArg(v_w_60_, v___x_65_, v___f_63_);
    return v___x_66_;
}
pub unsafe fn l_BitVec_iunfoldr___redArg___boxed(
    mut v_w_67_: *mut leanh::LeanObject,
    mut v_f_68_: *mut leanh::LeanObject,
    mut v_s_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_70_ = l_BitVec_iunfoldr___redArg(v_w_67_, v_f_68_, v_s_69_);
    leanh::lean_dec(v_w_67_);
    return v_res_70_;
}
pub unsafe fn l_BitVec_iunfoldr(
    mut v_w_71_: *mut leanh::LeanObject,
    mut v_00_u03b1_72_: *mut leanh::LeanObject,
    mut v_f_73_: *mut leanh::LeanObject,
    mut v_s_74_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_75_ = l_BitVec_iunfoldr___redArg(v_w_71_, v_f_73_, v_s_74_);
    return v___x_75_;
}
pub unsafe fn l_BitVec_iunfoldr___boxed(
    mut v_w_76_: *mut leanh::LeanObject,
    mut v_00_u03b1_77_: *mut leanh::LeanObject,
    mut v_f_78_: *mut leanh::LeanObject,
    mut v_s_79_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_80_ = l_BitVec_iunfoldr(v_w_76_, v_00_u03b1_77_, v_f_78_, v_s_79_);
    leanh::lean_dec(v_w_76_);
    return v_res_80_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_BitVec_Folds(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_BitVec_Folds(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_BitVec_Folds(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Folds(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_BitVec_Folds(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_BitVec_Folds(builtin);
}