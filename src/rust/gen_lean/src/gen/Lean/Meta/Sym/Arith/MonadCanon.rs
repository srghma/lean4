// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadCanon
// Imports: Lean.Meta.Sym.Arith.Types
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::Arith::Types::{
    initialize_Lean_Meta_Sym_Arith_Types, runtime_initialize_Lean_Meta_Sym_Arith_Types,
};
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0(
    mut v_inst_56_: *mut crate::leanh::LeanObject,
    mut v_inst_57_: *mut crate::leanh::LeanObject,
    mut v_e_58_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonExpr_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_59_ = crate::leanh::lean_ctor_get(v_inst_56_, 0);
    crate::leanh::lean_inc(v_canonExpr_59_);
    crate::leanh::lean_dec_ref(v_inst_56_);
    v___x_60_ = crate::leanh::lean_apply_1(v_canonExpr_59_, v_e_58_);
    v___x_61_ = crate::leanh::lean_apply_2(v_inst_57_, crate::leanh::lean_box(0), v___x_60_);
    return v___x_61_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1(
    mut v_inst_62_: *mut crate::leanh::LeanObject,
    mut v_inst_63_: *mut crate::leanh::LeanObject,
    mut v_e_64_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthInstance_x3f_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthInstance_x3f_65_ = crate::leanh::lean_ctor_get(v_inst_62_, 1);
    crate::leanh::lean_inc(v_synthInstance_x3f_65_);
    crate::leanh::lean_dec_ref(v_inst_62_);
    v___x_66_ = crate::leanh::lean_apply_1(v_synthInstance_x3f_65_, v_e_64_);
    v___x_67_ = crate::leanh::lean_apply_2(v_inst_63_, crate::leanh::lean_box(0), v___x_66_);
    return v___x_67_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg(
    mut v_inst_68_: *mut crate::leanh::LeanObject,
    mut v_inst_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_68_);
    crate::leanh::lean_inc_ref(v_inst_69_);
    v___f_70_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_70_, 0, v_inst_69_);
    crate::leanh::lean_closure_set(v___f_70_, 1, v_inst_68_);
    v___f_71_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_71_, 0, v_inst_69_);
    crate::leanh::lean_closure_set(v___f_71_, 1, v_inst_68_);
    v___x_72_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_72_, 0, v___f_70_);
    crate::leanh::lean_ctor_set(v___x_72_, 1, v___f_71_);
    return v___x_72_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift(
    mut v_m_73_: *mut crate::leanh::LeanObject,
    mut v_n_74_: *mut crate::leanh::LeanObject,
    mut v_inst_75_: *mut crate::leanh::LeanObject,
    mut v_inst_76_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_75_);
    crate::leanh::lean_inc_ref(v_inst_76_);
    v___f_77_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_77_, 0, v_inst_76_);
    crate::leanh::lean_closure_set(v___f_77_, 1, v_inst_75_);
    v___f_78_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_78_, 0, v_inst_76_);
    crate::leanh::lean_closure_set(v___f_78_, 1, v_inst_75_);
    v___x_79_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_79_, 0, v___f_77_);
    crate::leanh::lean_ctor_set(v___x_79_, 1, v___f_78_);
    return v___x_79_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_81_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0;
    v___x_82_ = l_Lean_stringToMessageData(v___x_81_);
    return v___x_82_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0(
    mut v_toPure_83_: *mut crate::leanh::LeanObject,
    mut v_type_84_: *mut crate::leanh::LeanObject,
    mut v_inst_85_: *mut crate::leanh::LeanObject,
    mut v_inst_86_: *mut crate::leanh::LeanObject,
    mut v_____x_87_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_87_) == 1 {
        let mut v_val_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_86_);
        crate::leanh::lean_dec_ref(v_inst_85_);
        crate::leanh::lean_dec_ref(v_type_84_);
        v_val_88_ = crate::leanh::lean_ctor_get(v_____x_87_, 0);
        crate::leanh::lean_inc(v_val_88_);
        crate::leanh::lean_dec_ref_known(v_____x_87_, 1);
        v___x_89_ = crate::leanh::lean_apply_2(v_toPure_83_, crate::leanh::lean_box(0), v_val_88_);
        return v___x_89_;
    } else {
        let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_____x_87_);
        crate::leanh::lean_dec(v_toPure_83_);
        v___x_90_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1_once
            ),
            _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1,
        );
        v___x_91_ = l_Lean_indentExpr(v_type_84_);
        v___x_92_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_92_, 0, v___x_90_);
        crate::leanh::lean_ctor_set(v___x_92_, 1, v___x_91_);
        v___x_93_ = l_Lean_throwError___redArg(v_inst_85_, v_inst_86_, v___x_92_);
        return v___x_93_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
    mut v_inst_94_: *mut crate::leanh::LeanObject,
    mut v_inst_95_: *mut crate::leanh::LeanObject,
    mut v_inst_96_: *mut crate::leanh::LeanObject,
    mut v_type_97_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_98_ = crate::leanh::lean_ctor_get(v_inst_94_, 0);
    v_toBind_99_ = crate::leanh::lean_ctor_get(v_inst_94_, 1);
    crate::leanh::lean_inc(v_toBind_99_);
    v_synthInstance_x3f_100_ = crate::leanh::lean_ctor_get(v_inst_96_, 1);
    crate::leanh::lean_inc(v_synthInstance_x3f_100_);
    crate::leanh::lean_dec_ref(v_inst_96_);
    v_toPure_101_ = crate::leanh::lean_ctor_get(v_toApplicative_98_, 1);
    crate::leanh::lean_inc(v_toPure_101_);
    crate::leanh::lean_inc_ref(v_type_97_);
    v___x_102_ = crate::leanh::lean_apply_1(v_synthInstance_x3f_100_, v_type_97_);
    v___f_103_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_103_, 0, v_toPure_101_);
    crate::leanh::lean_closure_set(v___f_103_, 1, v_type_97_);
    crate::leanh::lean_closure_set(v___f_103_, 2, v_inst_94_);
    crate::leanh::lean_closure_set(v___f_103_, 3, v_inst_95_);
    v___x_104_ = crate::leanh::lean_apply_4(
        v_toBind_99_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_102_,
        v___f_103_,
    );
    return v___x_104_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance(
    mut v_m_105_: *mut crate::leanh::LeanObject,
    mut v_inst_106_: *mut crate::leanh::LeanObject,
    mut v_inst_107_: *mut crate::leanh::LeanObject,
    mut v_inst_108_: *mut crate::leanh::LeanObject,
    mut v_type_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_MonadCanon(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_MonadCanon(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
}
