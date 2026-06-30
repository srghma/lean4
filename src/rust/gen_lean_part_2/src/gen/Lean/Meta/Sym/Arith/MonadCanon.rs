// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadCanon
// Imports: Lean.Meta.Sym.Arith.Types
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::Arith::Types::{
    initialize_Lean_Meta_Sym_Arith_Types, runtime_initialize_Lean_Meta_Sym_Arith_Types,
};
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 105, 110, 115, 116,
        97, 110, 99, 101, 0,
    ],
};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0(
    mut v_inst_56_: *mut leanh::LeanObject,
    mut v_inst_57_: *mut leanh::LeanObject,
    mut v_e_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonExpr_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_59_ = leanh::lean_ctor_get(v_inst_56_, 0);
    leanh::lean_inc(v_canonExpr_59_);
    leanh::lean_dec_ref(v_inst_56_);
    v___x_60_ = leanh::lean_apply_1(v_canonExpr_59_, v_e_58_);
    v___x_61_ = leanh::lean_apply_2(v_inst_57_, leanh::lean_box(0), v___x_60_);
    return v___x_61_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1(
    mut v_inst_62_: *mut leanh::LeanObject,
    mut v_inst_63_: *mut leanh::LeanObject,
    mut v_e_64_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_synthInstance_x3f_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_synthInstance_x3f_65_ = leanh::lean_ctor_get(v_inst_62_, 1);
    leanh::lean_inc(v_synthInstance_x3f_65_);
    leanh::lean_dec_ref(v_inst_62_);
    v___x_66_ = leanh::lean_apply_1(v_synthInstance_x3f_65_, v_e_64_);
    v___x_67_ = leanh::lean_apply_2(v_inst_63_, leanh::lean_box(0), v___x_66_);
    return v___x_67_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg(
    mut v_inst_68_: *mut leanh::LeanObject,
    mut v_inst_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_inst_68_);
    leanh::lean_inc_ref(v_inst_69_);
    v___f_70_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_70_, 0, v_inst_69_);
    leanh::lean_closure_set(v___f_70_, 1, v_inst_68_);
    v___f_71_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_71_, 0, v_inst_69_);
    leanh::lean_closure_set(v___f_71_, 1, v_inst_68_);
    v___x_72_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_72_, 0, v___f_70_);
    leanh::lean_ctor_set(v___x_72_, 1, v___f_71_);
    return v___x_72_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift(
    mut v_m_73_: *mut leanh::LeanObject,
    mut v_n_74_: *mut leanh::LeanObject,
    mut v_inst_75_: *mut leanh::LeanObject,
    mut v_inst_76_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_inst_75_);
    leanh::lean_inc_ref(v_inst_76_);
    v___f_77_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_77_, 0, v_inst_76_);
    leanh::lean_closure_set(v___f_77_, 1, v_inst_75_);
    v___f_78_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_78_, 0, v_inst_76_);
    leanh::lean_closure_set(v___f_78_, 1, v_inst_75_);
    v___x_79_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_79_, 0, v___f_77_);
    leanh::lean_ctor_set(v___x_79_, 1, v___f_78_);
    return v___x_79_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_81_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0;
    v___x_82_ = l_Lean_stringToMessageData(v___x_81_);
    return v___x_82_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0(
    mut v_toPure_83_: *mut leanh::LeanObject,
    mut v_type_84_: *mut leanh::LeanObject,
    mut v_inst_85_: *mut leanh::LeanObject,
    mut v_inst_86_: *mut leanh::LeanObject,
    mut v_____x_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_87_) == 1 {
        let mut v_val_88_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_86_);
        leanh::lean_dec_ref(v_inst_85_);
        leanh::lean_dec_ref(v_type_84_);
        v_val_88_ = leanh::lean_ctor_get(v_____x_87_, 0);
        leanh::lean_inc(v_val_88_);
        leanh::lean_dec_ref_known(v_____x_87_, 1);
        v___x_89_ = leanh::lean_apply_2(v_toPure_83_, leanh::lean_box(0), v_val_88_);
        return v___x_89_;
    } else {
        let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_91_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_92_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_93_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_____x_87_);
        leanh::lean_dec(v_toPure_83_);
        v___x_90_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1_once
            ),
            _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1,
        );
        v___x_91_ = l_Lean_indentExpr(v_type_84_);
        v___x_92_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_92_, 0, v___x_90_);
        leanh::lean_ctor_set(v___x_92_, 1, v___x_91_);
        v___x_93_ = l_Lean_throwError___redArg(v_inst_85_, v_inst_86_, v___x_92_);
        return v___x_93_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
    mut v_inst_94_: *mut leanh::LeanObject,
    mut v_inst_95_: *mut leanh::LeanObject,
    mut v_inst_96_: *mut leanh::LeanObject,
    mut v_type_97_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_98_ = leanh::lean_ctor_get(v_inst_94_, 0);
    v_toBind_99_ = leanh::lean_ctor_get(v_inst_94_, 1);
    leanh::lean_inc(v_toBind_99_);
    v_synthInstance_x3f_100_ = leanh::lean_ctor_get(v_inst_96_, 1);
    leanh::lean_inc(v_synthInstance_x3f_100_);
    leanh::lean_dec_ref(v_inst_96_);
    v_toPure_101_ = leanh::lean_ctor_get(v_toApplicative_98_, 1);
    leanh::lean_inc(v_toPure_101_);
    leanh::lean_inc_ref(v_type_97_);
    v___x_102_ = leanh::lean_apply_1(v_synthInstance_x3f_100_, v_type_97_);
    v___f_103_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_103_, 0, v_toPure_101_);
    leanh::lean_closure_set(v___f_103_, 1, v_type_97_);
    leanh::lean_closure_set(v___f_103_, 2, v_inst_94_);
    leanh::lean_closure_set(v___f_103_, 3, v_inst_95_);
    v___x_104_ = leanh::lean_apply_4(
        v_toBind_99_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_102_,
        v___f_103_,
    );
    return v___x_104_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance(
    mut v_m_105_: *mut leanh::LeanObject,
    mut v_inst_106_: *mut leanh::LeanObject,
    mut v_inst_107_: *mut leanh::LeanObject,
    mut v_inst_108_: *mut leanh::LeanObject,
    mut v_type_109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_110_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_106_,
        v_inst_107_,
        v_inst_108_,
        v_type_109_,
    );
    return v___x_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_MonadCanon(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_MonadCanon(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
}