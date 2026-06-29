// Lean compiler output
// Module: Lean.Data.OpenDecl
// Imports: Init.Data.ToString.Name Init.Data.ToString.Extra
use crate::r#gen::Init::Data::List::Basic::l_List_beq___redArg;
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, l_List_toString___redArg,
    runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_instToString___lam__0,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_replacePrefix;
use crate::r#gen::Init::Prelude::l_Lean_Name_beq___boxed;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::lean_name_eq;
pub static l_Lean_instBEqOpenDecl___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqOpenDecl_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqOpenDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqOpenDecl___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqOpenDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqOpenDecl___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_OpenDecl_instInhabited___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_OpenDecl_instInhabited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instInhabited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_OpenDecl_instInhabited: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instInhabited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [32, 104, 105, 100, 105, 110, 103, 32, 0],
};
static mut l_Lean_OpenDecl_instToString___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___lam__0___closed__1_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 134, 146, 32, 0],
};
static mut l_Lean_OpenDecl_instToString___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_OpenDecl_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_OpenDecl_instToString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_OpenDecl_instToString___closed__2_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_OpenDecl_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_OpenDecl_instToString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_OpenDecl_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_OpenDecl_instToString___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_rootNamespace___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [95, 114, 111, 111, 116, 95, 0],
    };
static mut l_Lean_rootNamespace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rootNamespace___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_rootNamespace___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_rootNamespace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            626731335300788152 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_rootNamespace___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rootNamespace___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_rootNamespace: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rootNamespace___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_OpenDecl_ctorIdx(
    mut v_x_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_117_) == 0 {
        let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_118_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_118_;
    } else {
        let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_119_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_119_;
    }
}
pub unsafe fn l_Lean_OpenDecl_ctorIdx___boxed(
    mut v_x_120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_121_ = l_Lean_OpenDecl_ctorIdx(v_x_120_);
    crate::leanh::lean_dec_ref(v_x_120_);
    return v_res_121_;
}
pub unsafe fn l_Lean_OpenDecl_ctorElim___redArg(
    mut v_t_122_: *mut crate::leanh::LeanObject,
    mut v_k_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ns_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_except_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ns_124_ = crate::leanh::lean_ctor_get(v_t_122_, 0);
    crate::leanh::lean_inc(v_ns_124_);
    v_except_125_ = crate::leanh::lean_ctor_get(v_t_122_, 1);
    crate::leanh::lean_inc(v_except_125_);
    crate::leanh::lean_dec_ref(v_t_122_);
    v___x_126_ = crate::leanh::lean_apply_2(v_k_123_, v_ns_124_, v_except_125_);
    return v___x_126_;
}
pub unsafe fn l_Lean_OpenDecl_ctorElim(
    mut v_motive_127_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_128_: *mut crate::leanh::LeanObject,
    mut v_t_129_: *mut crate::leanh::LeanObject,
    mut v_h_130_: *mut crate::leanh::LeanObject,
    mut v_k_131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_132_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_129_, v_k_131_);
    return v___x_132_;
}
pub unsafe fn l_Lean_OpenDecl_ctorElim___boxed(
    mut v_motive_133_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_134_: *mut crate::leanh::LeanObject,
    mut v_t_135_: *mut crate::leanh::LeanObject,
    mut v_h_136_: *mut crate::leanh::LeanObject,
    mut v_k_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_138_ =
        l_Lean_OpenDecl_ctorElim(v_motive_133_, v_ctorIdx_134_, v_t_135_, v_h_136_, v_k_137_);
    crate::leanh::lean_dec(v_ctorIdx_134_);
    return v_res_138_;
}
pub unsafe fn l_Lean_OpenDecl_simple_elim___redArg(
    mut v_t_139_: *mut crate::leanh::LeanObject,
    mut v_simple_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_141_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_139_, v_simple_140_);
    return v___x_141_;
}
pub unsafe fn l_Lean_OpenDecl_simple_elim(
    mut v_motive_142_: *mut crate::leanh::LeanObject,
    mut v_t_143_: *mut crate::leanh::LeanObject,
    mut v_h_144_: *mut crate::leanh::LeanObject,
    mut v_simple_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_146_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_143_, v_simple_145_);
    return v___x_146_;
}
pub unsafe fn l_Lean_OpenDecl_explicit_elim___redArg(
    mut v_t_147_: *mut crate::leanh::LeanObject,
    mut v_explicit_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_147_, v_explicit_148_);
    return v___x_149_;
}
pub unsafe fn l_Lean_OpenDecl_explicit_elim(
    mut v_motive_150_: *mut crate::leanh::LeanObject,
    mut v_t_151_: *mut crate::leanh::LeanObject,
    mut v_h_152_: *mut crate::leanh::LeanObject,
    mut v_explicit_153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_154_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_151_, v_explicit_153_);
    return v___x_154_;
}
pub unsafe fn l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(
    mut v_x_155_: *mut crate::leanh::LeanObject,
    mut v_x_156_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_157_: u8 = 0;
    let mut v___x_158_: u8 = 0;
    let mut v___x_159_: u8 = 0;
    let mut v_head_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_155_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_156_) == 0 {
                        v___x_157_ = 1;
                        return v___x_157_;
                    } else {
                        v___x_158_ = 0;
                        return v___x_158_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_156_) == 0 {
                        v___x_159_ = 0;
                        return v___x_159_;
                    } else {
                        v_head_160_ = crate::leanh::lean_ctor_get(v_x_155_, 0);
                        v_tail_161_ = crate::leanh::lean_ctor_get(v_x_155_, 1);
                        v_head_162_ = crate::leanh::lean_ctor_get(v_x_156_, 0);
                        v_tail_163_ = crate::leanh::lean_ctor_get(v_x_156_, 1);
                        v___x_164_ = lean_name_eq(v_head_160_, v_head_162_);
                        if v___x_164_ == 0 {
                            return v___x_164_;
                        } else {
                            v_x_155_ = v_tail_161_;
                            v_x_156_ = v_tail_163_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0___boxed(
    mut v_x_166_: *mut crate::leanh::LeanObject,
    mut v_x_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_168_: u8 = 0;
    let mut v_r_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(v_x_166_, v_x_167_);
    crate::leanh::lean_dec(v_x_167_);
    crate::leanh::lean_dec(v_x_166_);
    v_r_169_ = crate::leanh::lean_box((v_res_168_) as usize);
    return v_r_169_;
}
pub unsafe fn l_Lean_instBEqOpenDecl_beq(
    mut v_x_170_: *mut crate::leanh::LeanObject,
    mut v_x_171_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_170_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_171_) == 0 {
            let mut v_ns_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_except_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ns_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_except_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_176_: u8 = 0;
            v_ns_172_ = crate::leanh::lean_ctor_get(v_x_170_, 0);
            v_except_173_ = crate::leanh::lean_ctor_get(v_x_170_, 1);
            v_ns_174_ = crate::leanh::lean_ctor_get(v_x_171_, 0);
            v_except_175_ = crate::leanh::lean_ctor_get(v_x_171_, 1);
            v___x_176_ = lean_name_eq(v_ns_172_, v_ns_174_);
            if v___x_176_ == 0 {
                return v___x_176_;
            } else {
                let mut v___x_177_: u8 = 0;
                v___x_177_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(
                    v_except_173_,
                    v_except_175_,
                );
                return v___x_177_;
            }
        } else {
            let mut v___x_178_: u8 = 0;
            v___x_178_ = 0;
            return v___x_178_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_171_) == 1 {
            let mut v_id_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_declName_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_declName_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_183_: u8 = 0;
            v_id_179_ = crate::leanh::lean_ctor_get(v_x_170_, 0);
            v_declName_180_ = crate::leanh::lean_ctor_get(v_x_170_, 1);
            v_id_181_ = crate::leanh::lean_ctor_get(v_x_171_, 0);
            v_declName_182_ = crate::leanh::lean_ctor_get(v_x_171_, 1);
            v___x_183_ = lean_name_eq(v_id_179_, v_id_181_);
            if v___x_183_ == 0 {
                return v___x_183_;
            } else {
                let mut v___x_184_: u8 = 0;
                v___x_184_ = lean_name_eq(v_declName_180_, v_declName_182_);
                return v___x_184_;
            }
        } else {
            let mut v___x_185_: u8 = 0;
            v___x_185_ = 0;
            return v___x_185_;
        }
    }
}
pub unsafe fn l_Lean_instBEqOpenDecl_beq___boxed(
    mut v_x_186_: *mut crate::leanh::LeanObject,
    mut v_x_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_188_: u8 = 0;
    let mut v_r_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_188_ = l_Lean_instBEqOpenDecl_beq(v_x_186_, v_x_187_);
    crate::leanh::lean_dec_ref(v_x_187_);
    crate::leanh::lean_dec_ref(v_x_186_);
    v_r_189_ = crate::leanh::lean_box((v_res_188_) as usize);
    return v_r_189_;
}
pub unsafe fn l_Lean_OpenDecl_instToString___lam__0(
    mut v___x_198_: *mut crate::leanh::LeanObject,
    mut v___f_199_: *mut crate::leanh::LeanObject,
    mut v_decl_200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_decl_200_) == 0 {
        let mut v_ns_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_except_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_203_: u8 = 0;
        let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_206_: u8 = 0;
        v_ns_201_ = crate::leanh::lean_ctor_get(v_decl_200_, 0);
        crate::leanh::lean_inc(v_ns_201_);
        v_except_202_ = crate::leanh::lean_ctor_get(v_decl_200_, 1);
        crate::leanh::lean_inc_n(v_except_202_, 2);
        crate::leanh::lean_dec_ref_known(v_decl_200_, 2);
        v___x_203_ = 1;
        v___x_204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_ns_201_, v___x_203_,
        );
        v___x_205_ = crate::leanh::lean_box(0);
        v___x_206_ = l_List_beq___redArg(v___x_198_, v_except_202_, v___x_205_);
        if v___x_206_ == 0 {
            let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_207_ = l_Lean_OpenDecl_instToString___lam__0___closed__0;
            v___x_208_ = l_List_toString___redArg(v___f_199_, v_except_202_);
            v___x_209_ = lean_string_append(v___x_207_, v___x_208_);
            crate::leanh::lean_dec_ref(v___x_208_);
            v___x_210_ = lean_string_append(v___x_204_, v___x_209_);
            crate::leanh::lean_dec_ref(v___x_209_);
            return v___x_210_;
        } else {
            crate::leanh::lean_dec(v_except_202_);
            crate::leanh::lean_dec_ref(v___f_199_);
            return v___x_204_;
        }
    } else {
        let mut v_id_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_213_: u8 = 0;
        let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_199_);
        crate::leanh::lean_dec_ref(v___x_198_);
        v_id_211_ = crate::leanh::lean_ctor_get(v_decl_200_, 0);
        crate::leanh::lean_inc(v_id_211_);
        v_declName_212_ = crate::leanh::lean_ctor_get(v_decl_200_, 1);
        crate::leanh::lean_inc(v_declName_212_);
        crate::leanh::lean_dec_ref_known(v_decl_200_, 2);
        v___x_213_ = 1;
        v___x_214_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_id_211_, v___x_213_,
        );
        v___x_215_ = l_Lean_OpenDecl_instToString___lam__0___closed__1;
        v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
        v___x_217_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_declName_212_,
            v___x_213_,
        );
        v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
        crate::leanh::lean_dec_ref(v___x_217_);
        return v___x_218_;
    }
}
pub unsafe fn l_Lean_removeRoot(
    mut v_n_229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ = l_Lean_rootNamespace;
    v___x_231_ = crate::leanh::lean_box(0);
    v___x_232_ = l_Lean_Name_replacePrefix(v_n_229_, v___x_230_, v___x_231_);
    return v___x_232_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_OpenDecl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_OpenDecl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_OpenDecl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_OpenDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_OpenDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_OpenDecl(builtin);
}
