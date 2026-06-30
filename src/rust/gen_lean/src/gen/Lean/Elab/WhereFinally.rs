// Lean compiler output
// Module: Lean.Elab.WhereFinally
// Imports: Lean.Parser.Term
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isMissing};
use crate::r#gen::Lean::Exception::l_Lean_throwErrorAt___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, runtime_initialize_Lean_Parser_Term,
};
pub static l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedWhereFinallyView_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedWhereFinallyView: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_WhereFinallyView_none: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_mkWhereFinallyView___redArg___closed__0_value:
    leanh::LeanStringObject<93> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 93,
    m_capacity: 93,
    m_length: 92,
    m_data: [
        96, 119, 104, 101, 114, 101, 32, 46, 46, 46, 32, 102, 105, 110, 97, 108, 108, 121, 96, 32,
        100, 111, 101, 115, 32, 110, 111, 116, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32,
        115, 117, 112, 112, 111, 114, 116, 32, 97, 110, 121, 32, 110, 97, 109, 101, 100, 32, 115,
        117, 98, 45, 115, 101, 99, 116, 105, 111, 110, 115, 32, 96, 124, 32, 115, 101, 99, 116,
        105, 111, 110, 78, 97, 109, 101, 32, 61, 62, 32, 46, 46, 46, 96, 0,
    ],
};
static mut l_Lean_Elab_mkWhereFinallyView___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkWhereFinallyView___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkWhereFinallyView___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkWhereFinallyView___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_WhereFinallyView_isNone(
    mut v_o_78_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_ref_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tactic_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_81_: u8 = 0;
    v_ref_79_ = leanh::lean_ctor_get(v_o_78_, 0);
    v_tactic_80_ = leanh::lean_ctor_get(v_o_78_, 1);
    v___x_81_ = l_Lean_Syntax_isMissing(v_ref_79_);
    if v___x_81_ == 0 {
        return v___x_81_;
    } else {
        let mut v___x_82_: u8 = 0;
        v___x_82_ = l_Lean_Syntax_isMissing(v_tactic_80_);
        return v___x_82_;
    }
}
pub unsafe fn l_Lean_Elab_WhereFinallyView_isNone___boxed(
    mut v_o_83_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_84_: u8 = 0;
    let mut v_r_85_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_84_ = l_Lean_Elab_WhereFinallyView_isNone(v_o_83_);
    leanh::lean_dec_ref(v_o_83_);
    v_r_85_ = leanh::lean_box((v_res_84_) as usize);
    return v_r_85_;
}
pub unsafe fn l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(
    mut v_inst_86_: *mut leanh::LeanObject,
    mut v_whereFinally_87_: *mut leanh::LeanObject,
    mut v_____r_88_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_92_: u8 = 0;
    let mut v_toPure_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tactic_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_100_: u8 = 0;
    let mut v_unused_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_89_ = leanh::lean_ctor_get(v_inst_86_, 0);
                v_isSharedCheck_100_ = (!leanh::lean_is_exclusive(v_inst_86_)) as u8;
                if v_isSharedCheck_100_ == 0 {
                    v_unused_101_ = leanh::lean_ctor_get(v_inst_86_, 1);
                    leanh::lean_dec(v_unused_101_);
                    v___x_91_ = v_inst_86_;
                    v_isShared_92_ = v_isSharedCheck_100_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_89_);
                    leanh::lean_dec(v_inst_86_);
                    v___x_91_ = leanh::lean_box(0);
                    v_isShared_92_ = v_isSharedCheck_100_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_93_ = leanh::lean_ctor_get(v_toApplicative_89_, 1);
                leanh::lean_inc(v_toPure_93_);
                leanh::lean_dec_ref(v_toApplicative_89_);
                v___x_94_ = leanh::lean_unsigned_to_nat(1);
                v_tactic_95_ = l_Lean_Syntax_getArg(v_whereFinally_87_, v___x_94_);
                if v_isShared_92_ == 0 {
                    leanh::lean_ctor_set(v___x_91_, 1, v_tactic_95_);
                    leanh::lean_ctor_set(v___x_91_, 0, v_whereFinally_87_);
                    v___x_97_ = v___x_91_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_99_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_99_, 0, v_whereFinally_87_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_99_, 1, v_tactic_95_);
                    v___x_97_ = v_reuseFailAlloc_99_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_98_ =
                    leanh::lean_apply_2(v_toPure_93_, leanh::lean_box(0), v___x_97_);
                return v___x_98_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_mkWhereFinallyView___redArg___lam__1(
    mut v___f_102_: *mut leanh::LeanObject,
    mut v_____r_103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_104_ = leanh::lean_apply_1(v___f_102_, v_____r_103_);
    return v___x_104_;
}
pub unsafe fn _init_l_Lean_Elab_mkWhereFinallyView___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_106_ = l_Lean_Elab_mkWhereFinallyView___redArg___closed__0;
    v___x_107_ = l_Lean_stringToMessageData(v___x_106_);
    return v___x_107_;
}
pub unsafe fn l_Lean_Elab_mkWhereFinallyView___redArg(
    mut v_inst_108_: *mut leanh::LeanObject,
    mut v_inst_109_: *mut leanh::LeanObject,
    mut v_stx_110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_whereFinally_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: u8 = 0;
    let mut v___f_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: u8 = 0;
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_131_: u8 = 0;
    let mut v_toPure_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_138_: u8 = 0;
    let mut v_unused_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_111_ = leanh::lean_unsigned_to_nat(2);
                v___x_112_ = l_Lean_Syntax_getArg(v_stx_110_, v___x_111_);
                v___x_113_ = leanh::lean_unsigned_to_nat(0);
                v_whereFinally_114_ = l_Lean_Syntax_getArg(v___x_112_, v___x_113_);
                leanh::lean_dec(v___x_112_);
                v___x_115_ = l_Lean_Syntax_isMissing(v_whereFinally_114_);
                if v___x_115_ == 0 {
                    leanh::lean_inc(v_whereFinally_114_);
                    leanh::lean_inc_ref(v_inst_108_);
                    v___f_116_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_mkWhereFinallyView___redArg___lam__0 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_116_, 0, v_inst_108_);
                    leanh::lean_closure_set(v___f_116_, 1, v_whereFinally_114_);
                    v___f_117_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_mkWhereFinallyView___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_117_, 0, v___f_116_);
                    v___x_123_ = l_Lean_Syntax_getArg(v_whereFinally_114_, v___x_111_);
                    v___x_124_ = l_Lean_Syntax_getArg(v___x_123_, v___x_113_);
                    leanh::lean_dec(v___x_123_);
                    v___x_125_ = l_Lean_Syntax_isMissing(v___x_124_);
                    leanh::lean_dec(v___x_124_);
                    if v___x_125_ == 0 {
                        leanh::lean_dec(v_whereFinally_114_);
                        state = 1;
                        continue;
                    } else {
                        if v___x_115_ == 0 {
                            leanh::lean_dec_ref(v___f_117_);
                            leanh::lean_dec(v_stx_110_);
                            leanh::lean_dec_ref(v_inst_109_);
                            v___x_126_ = leanh::lean_box(0);
                            v___x_127_ = l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(
                                v_inst_108_,
                                v_whereFinally_114_,
                                v___x_126_,
                            );
                            return v___x_127_;
                        } else {
                            leanh::lean_dec(v_whereFinally_114_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_whereFinally_114_);
                    leanh::lean_dec_ref(v_inst_109_);
                    v_toApplicative_128_ = leanh::lean_ctor_get(v_inst_108_, 0);
                    v_isSharedCheck_138_ = (!leanh::lean_is_exclusive(v_inst_108_)) as u8;
                    if v_isSharedCheck_138_ == 0 {
                        v_unused_139_ = leanh::lean_ctor_get(v_inst_108_, 1);
                        leanh::lean_dec(v_unused_139_);
                        v___x_130_ = v_inst_108_;
                        v_isShared_131_ = v_isSharedCheck_138_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_toApplicative_128_);
                        leanh::lean_dec(v_inst_108_);
                        v___x_130_ = leanh::lean_box(0);
                        v_isShared_131_ = v_isSharedCheck_138_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_toBind_119_ = leanh::lean_ctor_get(v_inst_108_, 1);
                leanh::lean_inc(v_toBind_119_);
                v___x_120_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_mkWhereFinallyView___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_mkWhereFinallyView___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_mkWhereFinallyView___redArg___closed__1,
                );
                v___x_121_ =
                    l_Lean_throwErrorAt___redArg(v_inst_108_, v_inst_109_, v_stx_110_, v___x_120_);
                v___x_122_ = leanh::lean_apply_4(
                    v_toBind_119_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_121_,
                    v___f_117_,
                );
                return v___x_122_;
            }
            2 => {
                v_toPure_132_ = leanh::lean_ctor_get(v_toApplicative_128_, 1);
                leanh::lean_inc(v_toPure_132_);
                leanh::lean_dec_ref(v_toApplicative_128_);
                v___x_133_ = leanh::lean_box(0);
                if v_isShared_131_ == 0 {
                    leanh::lean_ctor_set(v___x_130_, 1, v___x_133_);
                    leanh::lean_ctor_set(v___x_130_, 0, v_stx_110_);
                    v___x_135_ = v___x_130_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_137_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_137_, 0, v_stx_110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_133_);
                    v___x_135_ = v_reuseFailAlloc_137_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_136_ = leanh::lean_apply_2(
                    v_toPure_132_,
                    leanh::lean_box(0),
                    v___x_135_,
                );
                return v___x_136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_mkWhereFinallyView(
    mut v_m_140_: *mut leanh::LeanObject,
    mut v_inst_141_: *mut leanh::LeanObject,
    mut v_inst_142_: *mut leanh::LeanObject,
    mut v_stx_143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_144_ = l_Lean_Elab_mkWhereFinallyView___redArg(v_inst_141_, v_inst_142_, v_stx_143_);
    return v___x_144_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_WhereFinally(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_WhereFinally(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_WhereFinally(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_WhereFinally(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_WhereFinally(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_WhereFinally(builtin);
}