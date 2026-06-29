// Lean compiler output
// Module: Lean.PrivateName
// Imports: Init.Notation Init.Data.Option.Coe
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::lean_imports_rs::Init::Prelude::{lean_name_eq, lean_nat_dec_eq};
pub static l_Lean_privateHeader___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0],
    };
static mut l_Lean_privateHeader___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_privateHeader___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_privateHeader___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_privateHeader___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11079354408986465895 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_privateHeader___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_privateHeader___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_privateHeader: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_privateHeader___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_mkPrivateNameCore(
    mut v_mainModule_79_: *mut crate::leanh::LeanObject,
    mut v_n_80_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_81_ = l_Lean_privateHeader;
    v___x_82_ = l_Lean_Name_append(v___x_81_, v_mainModule_79_);
    v___x_83_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_84_ = l_Lean_Name_num___override(v___x_82_, v___x_83_);
    v___x_85_ = l_Lean_Name_append(v___x_84_, v_n_80_);
    return v___x_85_;
}
pub unsafe fn l_Lean_isPrivateName(mut v_x_86_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_87_: u8 = 0;
    let mut v_pre_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_90_: u8 = 0;
    let mut v_pre_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_86_) {
                0 => {
                    v___x_87_ = 0;
                    return v___x_87_;
                }
                1 => {
                    v_pre_88_ = crate::leanh::lean_ctor_get(v_x_86_, 0);
                    v___x_89_ = l_Lean_privateHeader;
                    v___x_90_ = lean_name_eq(v_x_86_, v___x_89_);
                    if v___x_90_ == 0 {
                        v_x_86_ = v_pre_88_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_90_;
                    }
                }
                _ => {
                    v_pre_92_ = crate::leanh::lean_ctor_get(v_x_86_, 0);
                    v_x_86_ = v_pre_92_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isPrivateName___boxed(
    mut v_x_94_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_95_: u8 = 0;
    let mut v_r_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_95_ = l_Lean_isPrivateName(v_x_94_);
    crate::leanh::lean_dec(v_x_94_);
    v_r_96_ = crate::leanh::lean_box((v_res_95_) as usize);
    return v_r_96_;
}
pub unsafe fn lean_is_private_name(mut v_n_97_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_98_: u8 = 0;
    v___x_98_ = l_Lean_isPrivateName(v_n_97_);
    crate::leanh::lean_dec(v_n_97_);
    return v___x_98_;
}
pub unsafe fn l_Lean_isPrivateNameExport___boxed(
    mut v_n_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_100_: u8 = 0;
    let mut v_r_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_100_ = lean_is_private_name(v_n_99_);
    v_r_101_ = crate::leanh::lean_box((v_res_100_) as usize);
    return v_r_101_;
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(
    mut v_n_102_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: u8 = 0;
    let mut v_pre_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_103_ = l_Lean_privateHeader;
                v___x_104_ = lean_name_eq(v_n_102_, v___x_103_);
                if v___x_104_ == 0 {
                    if crate::leanh::lean_obj_tag(v_n_102_) == 1 {
                        v_pre_105_ = crate::leanh::lean_ctor_get(v_n_102_, 0);
                        v_n_102_ = v_pre_105_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_104_;
                    }
                } else {
                    return v___x_104_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go___boxed(
    mut v_n_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_108_: u8 = 0;
    let mut v_r_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_108_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_n_107_);
    crate::leanh::lean_dec(v_n_107_);
    v_r_109_ = crate::leanh::lean_box((v_res_108_) as usize);
    return v_r_109_;
}
pub unsafe fn l_Lean_isPrivatePrefix(mut v_n_110_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_n_110_) == 2 {
        let mut v_pre_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_i_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_114_: u8 = 0;
        v_pre_111_ = crate::leanh::lean_ctor_get(v_n_110_, 0);
        v_i_112_ = crate::leanh::lean_ctor_get(v_n_110_, 1);
        v___x_113_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_114_ = lean_nat_dec_eq(v_i_112_, v___x_113_);
        if v___x_114_ == 0 {
            return v___x_114_;
        } else {
            let mut v___x_115_: u8 = 0;
            v___x_115_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_pre_111_);
            return v___x_115_;
        }
    } else {
        let mut v___x_116_: u8 = 0;
        v___x_116_ = 0;
        return v___x_116_;
    }
}
pub unsafe fn l_Lean_isPrivatePrefix___boxed(
    mut v_n_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_118_: u8 = 0;
    let mut v_r_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Lean_isPrivatePrefix(v_n_117_);
    crate::leanh::lean_dec(v_n_117_);
    v_r_119_ = crate::leanh::lean_box((v_res_118_) as usize);
    return v_r_119_;
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(
    mut v_n_120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_n_120_) {
        0 => {
            return v_n_120_;
        }
        1 => {
            let mut v_pre_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_121_ = crate::leanh::lean_ctor_get(v_n_120_, 0);
            crate::leanh::lean_inc(v_pre_121_);
            v_str_122_ = crate::leanh::lean_ctor_get(v_n_120_, 1);
            crate::leanh::lean_inc_ref(v_str_122_);
            crate::leanh::lean_dec_ref_known(v_n_120_, 2);
            v___x_123_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_pre_121_);
            v___x_124_ = l_Lean_Name_str___override(v___x_123_, v_str_122_);
            return v___x_124_;
        }
        _ => {
            let mut v_pre_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_127_: u8 = 0;
            v_pre_125_ = crate::leanh::lean_ctor_get(v_n_120_, 0);
            crate::leanh::lean_inc(v_pre_125_);
            v_i_126_ = crate::leanh::lean_ctor_get(v_n_120_, 1);
            crate::leanh::lean_inc(v_i_126_);
            v___x_127_ = l_Lean_isPrivatePrefix(v_n_120_);
            crate::leanh::lean_dec_ref_known(v_n_120_, 2);
            if v___x_127_ == 0 {
                let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_128_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_pre_125_);
                v___x_129_ = l_Lean_Name_num___override(v___x_128_, v_i_126_);
                return v___x_129_;
            } else {
                let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_i_126_);
                crate::leanh::lean_dec(v_pre_125_);
                v___x_130_ = crate::leanh::lean_box(0);
                return v___x_130_;
            }
        }
    }
}
pub unsafe fn lean_private_to_user_name(
    mut v_n_131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_132_: u8 = 0;
    v___x_132_ = l_Lean_isPrivateName(v_n_131_);
    if v___x_132_ == 0 {
        let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_n_131_);
        v___x_133_ = crate::leanh::lean_box(0);
        return v___x_133_;
    } else {
        let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_134_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_n_131_);
        v___x_135_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_135_, 0, v___x_134_);
        return v___x_135_;
    }
}
pub unsafe fn l_Lean_privateToUserName(
    mut v_n_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_137_: u8 = 0;
    v___x_137_ = l_Lean_isPrivateName(v_n_136_);
    if v___x_137_ == 0 {
        return v_n_136_;
    } else {
        let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_138_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_n_136_);
        return v___x_138_;
    }
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_privatePrefixAux(
    mut v_x_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pre_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_139_) == 1 {
                    v_pre_140_ = crate::leanh::lean_ctor_get(v_x_139_, 0);
                    v_x_139_ = v_pre_140_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_x_139_);
                    return v_x_139_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_privatePrefixAux___boxed(
    mut v_x_142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_143_ = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(v_x_142_);
    crate::leanh::lean_dec(v_x_142_);
    return v_res_143_;
}
pub unsafe fn lean_private_prefix(
    mut v_n_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_145_: u8 = 0;
    v___x_145_ = l_Lean_isPrivateName(v_n_144_);
    if v___x_145_ == 0 {
        let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_n_144_);
        v___x_146_ = crate::leanh::lean_box(0);
        return v___x_146_;
    } else {
        let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_147_ = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(v_n_144_);
        crate::leanh::lean_dec(v_n_144_);
        v___x_148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_148_, 0, v___x_147_);
        return v___x_148_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrivateName(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrivateName(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrivateName(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrivateName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_PrivateName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_PrivateName(builtin);
}
