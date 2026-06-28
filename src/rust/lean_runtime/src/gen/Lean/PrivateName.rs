// Lean compiler output
// Module: Lean.PrivateName
// Imports: Init.Notation Init.Data.Option.Coe
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::lean_imports_rs::Init::Prelude::{lean_name_eq, lean_nat_dec_eq};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_privateHeader___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_privateHeader___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_privateHeader___closed__0_value) as *mut LeanObject;
pub static l_Lean_privateHeader___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_privateHeader___closed__0_value) as *mut LeanObject,
        11079354408986465895 as *mut LeanObject,
    ],
};
static mut l_Lean_privateHeader___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_privateHeader___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_privateHeader: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_privateHeader___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_mkPrivateNameCore(
    mut v_mainModule_79_: *mut LeanObject,
    mut v_n_80_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
    v___x_81_ = l_Lean_privateHeader;
    v___x_82_ = l_Lean_Name_append(v___x_81_, v_mainModule_79_);
    v___x_83_ = lean_unsigned_to_nat(0);
    v___x_84_ = l_Lean_Name_num___override(v___x_82_, v___x_83_);
    v___x_85_ = l_Lean_Name_append(v___x_84_, v_n_80_);
    return v___x_85_;
}
pub unsafe fn l_Lean_isPrivateName(mut v_x_86_: *mut LeanObject) -> u8 {
    let mut v___x_87_: u8 = 0;
    let mut v_pre_88_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_90_: u8 = 0;
    let mut v_pre_92_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_86_) {
                0 => {
                    v___x_87_ = 0;
                    return v___x_87_;
                }
                1 => {
                    v_pre_88_ = lean_ctor_get(v_x_86_, 0);
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
                    v_pre_92_ = lean_ctor_get(v_x_86_, 0);
                    v_x_86_ = v_pre_92_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isPrivateName___boxed(mut v_x_94_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_95_: u8 = 0;
    let mut v_r_96_: *mut LeanObject = core::ptr::null_mut();
    v_res_95_ = l_Lean_isPrivateName(v_x_94_);
    lean_dec(v_x_94_);
    v_r_96_ = lean_box((v_res_95_) as usize);
    return v_r_96_;
}
pub unsafe fn lean_is_private_name(mut v_n_97_: *mut LeanObject) -> u8 {
    let mut v___x_98_: u8 = 0;
    v___x_98_ = l_Lean_isPrivateName(v_n_97_);
    lean_dec(v_n_97_);
    return v___x_98_;
}
pub unsafe fn l_Lean_isPrivateNameExport___boxed(mut v_n_99_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_100_: u8 = 0;
    let mut v_r_101_: *mut LeanObject = core::ptr::null_mut();
    v_res_100_ = lean_is_private_name(v_n_99_);
    v_r_101_ = lean_box((v_res_100_) as usize);
    return v_r_101_;
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(
    mut v_n_102_: *mut LeanObject,
) -> u8 {
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_104_: u8 = 0;
    let mut v_pre_105_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_103_ = l_Lean_privateHeader;
                v___x_104_ = lean_name_eq(v_n_102_, v___x_103_);
                if v___x_104_ == 0 {
                    if lean_obj_tag(v_n_102_) == 1 {
                        v_pre_105_ = lean_ctor_get(v_n_102_, 0);
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
    mut v_n_107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_108_: u8 = 0;
    let mut v_r_109_: *mut LeanObject = core::ptr::null_mut();
    v_res_108_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_n_107_);
    lean_dec(v_n_107_);
    v_r_109_ = lean_box((v_res_108_) as usize);
    return v_r_109_;
}
pub unsafe fn l_Lean_isPrivatePrefix(mut v_n_110_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_n_110_) == 2 {
        let mut v_pre_111_: *mut LeanObject = core::ptr::null_mut();
        let mut v_i_112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_114_: u8 = 0;
        v_pre_111_ = lean_ctor_get(v_n_110_, 0);
        v_i_112_ = lean_ctor_get(v_n_110_, 1);
        v___x_113_ = lean_unsigned_to_nat(0);
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
pub unsafe fn l_Lean_isPrivatePrefix___boxed(mut v_n_117_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_118_: u8 = 0;
    let mut v_r_119_: *mut LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Lean_isPrivatePrefix(v_n_117_);
    lean_dec(v_n_117_);
    v_r_119_ = lean_box((v_res_118_) as usize);
    return v_r_119_;
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(
    mut v_n_120_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_n_120_) {
        0 => {
            return v_n_120_;
        }
        1 => {
            let mut v_pre_121_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_122_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
            v_pre_121_ = lean_ctor_get(v_n_120_, 0);
            lean_inc(v_pre_121_);
            v_str_122_ = lean_ctor_get(v_n_120_, 1);
            lean_inc_ref(v_str_122_);
            lean_dec_ref_known(v_n_120_, 2);
            v___x_123_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_pre_121_);
            v___x_124_ = l_Lean_Name_str___override(v___x_123_, v_str_122_);
            return v___x_124_;
        }
        _ => {
            let mut v_pre_125_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_126_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_127_: u8 = 0;
            v_pre_125_ = lean_ctor_get(v_n_120_, 0);
            lean_inc(v_pre_125_);
            v_i_126_ = lean_ctor_get(v_n_120_, 1);
            lean_inc(v_i_126_);
            v___x_127_ = l_Lean_isPrivatePrefix(v_n_120_);
            lean_dec_ref_known(v_n_120_, 2);
            if v___x_127_ == 0 {
                let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
                v___x_128_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_pre_125_);
                v___x_129_ = l_Lean_Name_num___override(v___x_128_, v_i_126_);
                return v___x_129_;
            } else {
                let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_i_126_);
                lean_dec(v_pre_125_);
                v___x_130_ = lean_box(0);
                return v___x_130_;
            }
        }
    }
}
pub unsafe fn lean_private_to_user_name(mut v_n_131_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_132_: u8 = 0;
    v___x_132_ = l_Lean_isPrivateName(v_n_131_);
    if v___x_132_ == 0 {
        let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_n_131_);
        v___x_133_ = lean_box(0);
        return v___x_133_;
    } else {
        let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
        v___x_134_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_n_131_);
        v___x_135_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_135_, 0, v___x_134_);
        return v___x_135_;
    }
}
pub unsafe fn l_Lean_privateToUserName(mut v_n_136_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_137_: u8 = 0;
    v___x_137_ = l_Lean_isPrivateName(v_n_136_);
    if v___x_137_ == 0 {
        return v_n_136_;
    } else {
        let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
        v___x_138_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_n_136_);
        return v___x_138_;
    }
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_privatePrefixAux(
    mut v_x_139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pre_140_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_139_) == 1 {
                    v_pre_140_ = lean_ctor_get(v_x_139_, 0);
                    v_x_139_ = v_pre_140_;
                    state = 0;
                    continue;
                } else {
                    lean_inc(v_x_139_);
                    return v_x_139_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrivateName_0__Lean_privatePrefixAux___boxed(
    mut v_x_142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_143_: *mut LeanObject = core::ptr::null_mut();
    v_res_143_ = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(v_x_142_);
    lean_dec(v_x_142_);
    return v_res_143_;
}
pub unsafe fn lean_private_prefix(mut v_n_144_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_145_: u8 = 0;
    v___x_145_ = l_Lean_isPrivateName(v_n_144_);
    if v___x_145_ == 0 {
        let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_n_144_);
        v___x_146_ = lean_box(0);
        return v___x_146_;
    } else {
        let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_148_: *mut LeanObject = core::ptr::null_mut();
        v___x_147_ = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(v_n_144_);
        lean_dec(v_n_144_);
        v___x_148_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_148_, 0, v___x_147_);
        return v___x_148_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrivateName(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrivateName(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrivateName(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrivateName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_PrivateName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_PrivateName(builtin);
}
