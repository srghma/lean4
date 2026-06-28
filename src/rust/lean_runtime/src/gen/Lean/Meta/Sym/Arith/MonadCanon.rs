// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadCanon
// Imports: Lean.Meta.Sym.Arith.Types
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::Arith::Types::{
    initialize_Lean_Meta_Sym_Arith_Types, runtime_initialize_Lean_Meta_Sym_Arith_Types,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_once, lean_obj_tag,
};
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0(
    mut v_inst_56_: *mut LeanObject,
    mut v_inst_57_: *mut LeanObject,
    mut v_e_58_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonExpr_59_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
    v_canonExpr_59_ = lean_ctor_get(v_inst_56_, 0);
    lean_inc(v_canonExpr_59_);
    lean_dec_ref(v_inst_56_);
    v___x_60_ = lean_apply_1(v_canonExpr_59_, v_e_58_);
    v___x_61_ = lean_apply_2(v_inst_57_, lean_box(0), v___x_60_);
    return v___x_61_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1(
    mut v_inst_62_: *mut LeanObject,
    mut v_inst_63_: *mut LeanObject,
    mut v_e_64_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthInstance_x3f_65_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
    v_synthInstance_x3f_65_ = lean_ctor_get(v_inst_62_, 1);
    lean_inc(v_synthInstance_x3f_65_);
    lean_dec_ref(v_inst_62_);
    v___x_66_ = lean_apply_1(v_synthInstance_x3f_65_, v_e_64_);
    v___x_67_ = lean_apply_2(v_inst_63_, lean_box(0), v___x_66_);
    return v___x_67_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg(
    mut v_inst_68_: *mut LeanObject,
    mut v_inst_69_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_inst_68_);
    lean_inc_ref(v_inst_69_);
    v___f_70_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_70_, 0, v_inst_69_);
    lean_closure_set(v___f_70_, 1, v_inst_68_);
    v___f_71_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_71_, 0, v_inst_69_);
    lean_closure_set(v___f_71_, 1, v_inst_68_);
    v___x_72_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_72_, 0, v___f_70_);
    lean_ctor_set(v___x_72_, 1, v___f_71_);
    return v___x_72_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift(
    mut v_m_73_: *mut LeanObject,
    mut v_n_74_: *mut LeanObject,
    mut v_inst_75_: *mut LeanObject,
    mut v_inst_76_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_78_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_inst_75_);
    lean_inc_ref(v_inst_76_);
    v___f_77_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_77_, 0, v_inst_76_);
    lean_closure_set(v___f_77_, 1, v_inst_75_);
    v___f_78_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadCanonOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_78_, 0, v_inst_76_);
    lean_closure_set(v___f_78_, 1, v_inst_75_);
    v___x_79_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_79_, 0, v___f_77_);
    lean_ctor_set(v___x_79_, 1, v___f_78_);
    return v___x_79_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
    v___x_81_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__0;
    v___x_82_ = l_Lean_stringToMessageData(v___x_81_);
    return v___x_82_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0(
    mut v_toPure_83_: *mut LeanObject,
    mut v_type_84_: *mut LeanObject,
    mut v_inst_85_: *mut LeanObject,
    mut v_inst_86_: *mut LeanObject,
    mut v_____x_87_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_87_) == 1 {
        let mut v_val_88_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_86_);
        lean_dec_ref(v_inst_85_);
        lean_dec_ref(v_type_84_);
        v_val_88_ = lean_ctor_get(v_____x_87_, 0);
        lean_inc(v_val_88_);
        lean_dec_ref_known(v_____x_87_, 1);
        v___x_89_ = lean_apply_2(v_toPure_83_, lean_box(0), v_val_88_);
        return v___x_89_;
    } else {
        let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____x_87_);
        lean_dec(v_toPure_83_);
        v___x_90_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1_once
            ),
            _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0___closed__1,
        );
        v___x_91_ = l_Lean_indentExpr(v_type_84_);
        v___x_92_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_92_, 0, v___x_90_);
        lean_ctor_set(v___x_92_, 1, v___x_91_);
        v___x_93_ = l_Lean_throwError___redArg(v_inst_85_, v_inst_86_, v___x_92_);
        return v___x_93_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
    mut v_inst_94_: *mut LeanObject,
    mut v_inst_95_: *mut LeanObject,
    mut v_inst_96_: *mut LeanObject,
    mut v_type_97_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_98_ = lean_ctor_get(v_inst_94_, 0);
    v_toBind_99_ = lean_ctor_get(v_inst_94_, 1);
    lean_inc(v_toBind_99_);
    v_synthInstance_x3f_100_ = lean_ctor_get(v_inst_96_, 1);
    lean_inc(v_synthInstance_x3f_100_);
    lean_dec_ref(v_inst_96_);
    v_toPure_101_ = lean_ctor_get(v_toApplicative_98_, 1);
    lean_inc(v_toPure_101_);
    lean_inc_ref(v_type_97_);
    v___x_102_ = lean_apply_1(v_synthInstance_x3f_100_, v_type_97_);
    v___f_103_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_103_, 0, v_toPure_101_);
    lean_closure_set(v___f_103_, 1, v_type_97_);
    lean_closure_set(v___f_103_, 2, v_inst_94_);
    lean_closure_set(v___f_103_, 3, v_inst_95_);
    v___x_104_ = lean_apply_4(
        v_toBind_99_,
        lean_box(0),
        lean_box(0),
        v___x_102_,
        v___f_103_,
    );
    return v___x_104_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance(
    mut v_m_105_: *mut LeanObject,
    mut v_inst_106_: *mut LeanObject,
    mut v_inst_107_: *mut LeanObject,
    mut v_inst_108_: *mut LeanObject,
    mut v_type_109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    v___x_110_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_106_,
        v_inst_107_,
        v_inst_108_,
        v_type_109_,
    );
    return v___x_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
}
