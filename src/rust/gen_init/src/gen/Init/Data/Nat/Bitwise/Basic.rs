// Lean compiler output
// Module: Init.Data.Nat.Bitwise.Basic
// Imports: Init.Grind.Tactics Init.Data.Nat.Div.Basic Init.MetaTypes Init.WFTactics
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::MetaTypes::{initialize_Init_MetaTypes, runtime_initialize_Init_MetaTypes};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::ffi::{
    lean_nat_land, lean_nat_lor, lean_nat_lxor, lean_nat_shiftl, lean_nat_shiftr,
};
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_div, lean_nat_mod,
};
pub static l_Nat_instAndOp___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Nat_instAndOp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instAndOp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Nat_instAndOp: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instAndOp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Nat_instOrOp___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Nat_instOrOp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instOrOp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Nat_instOrOp: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instOrOp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Nat_instXorOp___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Nat_instXorOp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instXorOp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Nat_instXorOp: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instXorOp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Nat_instShiftLeft___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Nat_instShiftLeft___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instShiftLeft___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Nat_instShiftLeft: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instShiftLeft___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Nat_instShiftRight___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Nat_instShiftRight___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instShiftRight___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Nat_instShiftRight: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instShiftRight___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_bitwise(
    mut v_f_84_: *mut crate::leanh::LeanObject,
    mut v_n_85_: *mut crate::leanh::LeanObject,
    mut v_m_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_88_: u8 = 0;
    v___x_87_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_88_ = lean_nat_dec_eq(v_n_85_, v___x_87_);
    if v___x_88_ == 0 {
        let mut v___x_89_: u8 = 0;
        v___x_89_ = lean_nat_dec_eq(v_m_86_, v___x_87_);
        if v___x_89_ == 0 {
            let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_x27_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_x27_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_96_: u8 = 0;
            let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_98_: u8 = 0;
            let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_102_: u8 = 0;
            v___x_90_ = crate::leanh::lean_unsigned_to_nat(2);
            v_n_x27_91_ = lean_nat_div(v_n_85_, v___x_90_);
            v_m_x27_92_ = lean_nat_div(v_m_86_, v___x_90_);
            crate::leanh::lean_inc_ref(v_f_84_);
            v_r_93_ = l_Nat_bitwise(v_f_84_, v_n_x27_91_, v_m_x27_92_);
            crate::leanh::lean_dec(v_m_x27_92_);
            crate::leanh::lean_dec(v_n_x27_91_);
            v___x_94_ = lean_nat_mod(v_n_85_, v___x_90_);
            v___x_95_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_96_ = lean_nat_dec_eq(v___x_94_, v___x_95_);
            crate::leanh::lean_dec(v___x_94_);
            v___x_97_ = lean_nat_mod(v_m_86_, v___x_90_);
            v___x_98_ = lean_nat_dec_eq(v___x_97_, v___x_95_);
            crate::leanh::lean_dec(v___x_97_);
            v___x_99_ = crate::leanh::lean_box((v___x_96_) as usize);
            v___x_100_ = crate::leanh::lean_box((v___x_98_) as usize);
            v___x_101_ = crate::leanh::lean_apply_2(v_f_84_, v___x_99_, v___x_100_);
            v___x_102_ = (crate::leanh::lean_unbox(v___x_101_) as u8);
            if v___x_102_ == 0 {
                let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_103_ = lean_nat_add(v_r_93_, v_r_93_);
                crate::leanh::lean_dec(v_r_93_);
                return v___x_103_;
            } else {
                let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_104_ = lean_nat_add(v_r_93_, v_r_93_);
                crate::leanh::lean_dec(v_r_93_);
                v___x_105_ = lean_nat_add(v___x_104_, v___x_95_);
                crate::leanh::lean_dec(v___x_104_);
                return v___x_105_;
            }
        } else {
            let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_109_: u8 = 0;
            v___x_106_ = crate::leanh::lean_box((v___x_89_) as usize);
            v___x_107_ = crate::leanh::lean_box((v___x_88_) as usize);
            v___x_108_ = crate::leanh::lean_apply_2(v_f_84_, v___x_106_, v___x_107_);
            v___x_109_ = (crate::leanh::lean_unbox(v___x_108_) as u8);
            if v___x_109_ == 0 {
                return v___x_87_;
            } else {
                crate::leanh::lean_inc(v_n_85_);
                return v_n_85_;
            }
        }
    } else {
        let mut v___x_110_: u8 = 0;
        let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_114_: u8 = 0;
        v___x_110_ = 0;
        v___x_111_ = crate::leanh::lean_box((v___x_110_) as usize);
        v___x_112_ = crate::leanh::lean_box((v___x_88_) as usize);
        v___x_113_ = crate::leanh::lean_apply_2(v_f_84_, v___x_111_, v___x_112_);
        v___x_114_ = (crate::leanh::lean_unbox(v___x_113_) as u8);
        if v___x_114_ == 0 {
            return v___x_87_;
        } else {
            crate::leanh::lean_inc(v_m_86_);
            return v_m_86_;
        }
    }
}
pub unsafe fn l_Nat_bitwise___boxed(
    mut v_f_115_: *mut crate::leanh::LeanObject,
    mut v_n_116_: *mut crate::leanh::LeanObject,
    mut v_m_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Nat_bitwise(v_f_115_, v_n_116_, v_m_117_);
    crate::leanh::lean_dec(v_m_117_);
    crate::leanh::lean_dec(v_n_116_);
    return v_res_118_;
}
pub unsafe fn l_Nat_land___boxed(
    mut v_a_00___x40___internal___hyg_121_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_123_ = lean_nat_land(
        v_a_00___x40___internal___hyg_121_,
        v_a_00___x40___internal___hyg_122_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_122_);
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_121_);
    return v_res_123_;
}
pub unsafe fn l_Nat_lor___boxed(
    mut v_a_00___x40___internal___hyg_126_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = lean_nat_lor(
        v_a_00___x40___internal___hyg_126_,
        v_a_00___x40___internal___hyg_127_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_127_);
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_126_);
    return v_res_128_;
}
pub unsafe fn l_Nat_xor___boxed(
    mut v_a_00___x40___internal___hyg_131_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_133_ = lean_nat_lxor(
        v_a_00___x40___internal___hyg_131_,
        v_a_00___x40___internal___hyg_132_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_132_);
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_131_);
    return v_res_133_;
}
pub unsafe fn l_Nat_shiftLeft___boxed(
    mut v_a_00___x40___internal___hyg_136_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_138_ = lean_nat_shiftl(
        v_a_00___x40___internal___hyg_136_,
        v_a_00___x40___internal___hyg_137_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_137_);
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_136_);
    return v_res_138_;
}
pub unsafe fn l_Nat_shiftRight___boxed(
    mut v_a_00___x40___internal___hyg_141_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_143_ = lean_nat_shiftr(
        v_a_00___x40___internal___hyg_141_,
        v_a_00___x40___internal___hyg_142_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_142_);
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_141_);
    return v_res_143_;
}
pub unsafe fn l_Nat_testBit(
    mut v_m_154_: *mut crate::leanh::LeanObject,
    mut v_n_155_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: u8 = 0;
    v___x_156_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_157_ = lean_nat_shiftr(v_m_154_, v_n_155_);
    v___x_158_ = lean_nat_land(v___x_156_, v___x_157_);
    crate::leanh::lean_dec(v___x_157_);
    v___x_159_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_160_ = lean_nat_dec_eq(v___x_158_, v___x_159_);
    crate::leanh::lean_dec(v___x_158_);
    if v___x_160_ == 0 {
        let mut v___x_161_: u8 = 0;
        v___x_161_ = 1;
        return v___x_161_;
    } else {
        let mut v___x_162_: u8 = 0;
        v___x_162_ = 0;
        return v___x_162_;
    }
}
pub unsafe fn l_Nat_testBit___boxed(
    mut v_m_163_: *mut crate::leanh::LeanObject,
    mut v_n_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_165_: u8 = 0;
    let mut v_r_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_165_ = l_Nat_testBit(v_m_163_, v_n_164_);
    crate::leanh::lean_dec(v_n_164_);
    crate::leanh::lean_dec(v_m_163_);
    v_r_166_ = crate::leanh::lean_box((v_res_165_) as usize);
    return v_r_166_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Bitwise_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Bitwise_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Bitwise_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Bitwise_Basic(builtin);
}
