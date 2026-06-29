// Lean compiler output
// Module: Lean.Compiler.LCNF.OtherDecl
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.MonoTypes Lean.Compiler.LCNF.ToImpureType
use crate::ffi::lean_st_ref_get;
use crate::r#gen::Lean::Compiler::LCNF::BaseTypes::l_Lean_Compiler_LCNF_getOtherDeclBaseType;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_getPhase___redArg,
    l_Lean_Compiler_LCNF_getPurity___redArg, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::MonoTypes::{
    initialize_Lean_Compiler_LCNF_MonoTypes, l_Lean_Compiler_LCNF_getOtherDeclMonoType,
    runtime_initialize_Lean_Compiler_LCNF_MonoTypes,
};
use crate::r#gen::Lean::Compiler::LCNF::ToImpureType::{
    initialize_Lean_Compiler_LCNF_ToImpureType, runtime_initialize_Lean_Compiler_LCNF_ToImpureType,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getOtherDeclType___closed__0_value: crate::leanh::LeanStringObject<
    40,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        103, 101, 116, 79, 116, 104, 101, 114, 68, 101, 99, 108, 84, 121, 112, 101, 32, 117, 110,
        115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 102, 111, 114, 32, 105, 109, 112, 117,
        114, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_getOtherDeclType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getOtherDeclType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getOtherDeclType___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_105_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_105_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_106_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0);
    v___x_107_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_107_, 0, v___x_106_);
    return v___x_107_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_108_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1);
    v___x_109_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_110_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_110_, 0, v___x_109_);
    crate::leanh::lean_ctor_set(v___x_110_, 1, v___x_109_);
    crate::leanh::lean_ctor_set(v___x_110_, 2, v___x_109_);
    crate::leanh::lean_ctor_set(v___x_110_, 3, v___x_109_);
    crate::leanh::lean_ctor_set(v___x_110_, 4, v___x_108_);
    crate::leanh::lean_ctor_set(v___x_110_, 5, v___x_108_);
    crate::leanh::lean_ctor_set(v___x_110_, 6, v___x_108_);
    crate::leanh::lean_ctor_set(v___x_110_, 7, v___x_108_);
    crate::leanh::lean_ctor_set(v___x_110_, 8, v___x_108_);
    crate::leanh::lean_ctor_set(v___x_110_, 9, v___x_108_);
    return v___x_110_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(
    mut v_msg_111_: *mut crate::leanh::LeanObject,
    mut v___y_112_: *mut crate::leanh::LeanObject,
    mut v___y_113_: *mut crate::leanh::LeanObject,
    mut v___y_114_: *mut crate::leanh::LeanObject,
    mut v___y_115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_125_: u8 = 0;
    let mut v_env_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_130_: u8 = 0;
    let mut v___x_131_: u8 = 0;
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_142_: u8 = 0;
    let mut v_unused_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_144_: u8 = 0;
    let mut v_a_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_148_: u8 = 0;
    let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_117_ = crate::leanh::lean_ctor_get(v___y_114_, 2);
                v_ref_118_ = crate::leanh::lean_ctor_get(v___y_114_, 5);
                v___x_119_ = lean_st_ref_get(v___y_115_);
                v___x_120_ = lean_st_ref_get(v___y_113_);
                v___x_121_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_112_);
                if crate::leanh::lean_obj_tag(v___x_121_) == 0 {
                    v_a_122_ = crate::leanh::lean_ctor_get(v___x_121_, 0);
                    v_isSharedCheck_144_ = (!crate::leanh::lean_is_exclusive(v___x_121_)) as u8;
                    if v_isSharedCheck_144_ == 0 {
                        v___x_124_ = v___x_121_;
                        v_isShared_125_ = v_isSharedCheck_144_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_122_);
                        crate::leanh::lean_dec(v___x_121_);
                        v___x_124_ = crate::leanh::lean_box(0);
                        v_isShared_125_ = v_isSharedCheck_144_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_120_);
                    crate::leanh::lean_dec(v___x_119_);
                    crate::leanh::lean_dec_ref(v_msg_111_);
                    v_a_145_ = crate::leanh::lean_ctor_get(v___x_121_, 0);
                    v_isSharedCheck_152_ = (!crate::leanh::lean_is_exclusive(v___x_121_)) as u8;
                    if v_isSharedCheck_152_ == 0 {
                        v___x_147_ = v___x_121_;
                        v_isShared_148_ = v_isSharedCheck_152_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_145_);
                        crate::leanh::lean_dec(v___x_121_);
                        v___x_147_ = crate::leanh::lean_box(0);
                        v_isShared_148_ = v_isSharedCheck_152_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_126_ = crate::leanh::lean_ctor_get(v___x_119_, 0);
                crate::leanh::lean_inc_ref(v_env_126_);
                crate::leanh::lean_dec(v___x_119_);
                v_lctx_127_ = crate::leanh::lean_ctor_get(v___x_120_, 0);
                v_isSharedCheck_142_ = (!crate::leanh::lean_is_exclusive(v___x_120_)) as u8;
                if v_isSharedCheck_142_ == 0 {
                    v_unused_143_ = crate::leanh::lean_ctor_get(v___x_120_, 1);
                    crate::leanh::lean_dec(v_unused_143_);
                    v___x_129_ = v___x_120_;
                    v_isShared_130_ = v_isSharedCheck_142_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_127_);
                    crate::leanh::lean_dec(v___x_120_);
                    v___x_129_ = crate::leanh::lean_box(0);
                    v_isShared_130_ = v_isSharedCheck_142_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_131_ = (crate::leanh::lean_unbox(v_a_122_) as u8);
                crate::leanh::lean_dec(v_a_122_);
                v___x_132_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_127_, v___x_131_);
                crate::leanh::lean_dec_ref(v_lctx_127_);
                v___x_133_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2);
                crate::leanh::lean_inc_ref(v_options_117_);
                v___x_134_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_134_, 0, v_env_126_);
                crate::leanh::lean_ctor_set(v___x_134_, 1, v___x_133_);
                crate::leanh::lean_ctor_set(v___x_134_, 2, v___x_132_);
                crate::leanh::lean_ctor_set(v___x_134_, 3, v_options_117_);
                if v_isShared_130_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_129_, 3);
                    crate::leanh::lean_ctor_set(v___x_129_, 1, v_msg_111_);
                    crate::leanh::lean_ctor_set(v___x_129_, 0, v___x_134_);
                    v___x_136_ = v___x_129_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_141_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_141_, 1, v_msg_111_);
                    v___x_136_ = v_reuseFailAlloc_141_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_ref_118_);
                v___x_137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_137_, 0, v_ref_118_);
                crate::leanh::lean_ctor_set(v___x_137_, 1, v___x_136_);
                if v_isShared_125_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_124_, 1);
                    crate::leanh::lean_ctor_set(v___x_124_, 0, v___x_137_);
                    v___x_139_ = v___x_124_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
                    v___x_139_ = v_reuseFailAlloc_140_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_139_;
            }
            5 => {
                if v_isShared_148_ == 0 {
                    v___x_150_ = v___x_147_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_151_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
                    v___x_150_ = v_reuseFailAlloc_151_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___boxed(
    mut v_msg_153_: *mut crate::leanh::LeanObject,
    mut v___y_154_: *mut crate::leanh::LeanObject,
    mut v___y_155_: *mut crate::leanh::LeanObject,
    mut v___y_156_: *mut crate::leanh::LeanObject,
    mut v___y_157_: *mut crate::leanh::LeanObject,
    mut v___y_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_159_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(
        v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_,
    );
    crate::leanh::lean_dec(v___y_157_);
    crate::leanh::lean_dec_ref(v___y_156_);
    crate::leanh::lean_dec(v___y_155_);
    crate::leanh::lean_dec_ref(v___y_154_);
    return v_res_159_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
    mut v_msg_161_: *mut crate::leanh::LeanObject,
    mut v___y_162_: *mut crate::leanh::LeanObject,
    mut v___y_163_: *mut crate::leanh::LeanObject,
    mut v___y_164_: *mut crate::leanh::LeanObject,
    mut v___y_165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_167_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(
        v_msg_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_,
    );
    return v___x_167_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___boxed(
    mut v_00_u03b1_168_: *mut crate::leanh::LeanObject,
    mut v_msg_169_: *mut crate::leanh::LeanObject,
    mut v___y_170_: *mut crate::leanh::LeanObject,
    mut v___y_171_: *mut crate::leanh::LeanObject,
    mut v___y_172_: *mut crate::leanh::LeanObject,
    mut v___y_173_: *mut crate::leanh::LeanObject,
    mut v___y_174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_175_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(
        v_00_u03b1_168_,
        v_msg_169_,
        v___y_170_,
        v___y_171_,
        v___y_172_,
        v___y_173_,
    );
    crate::leanh::lean_dec(v___y_173_);
    crate::leanh::lean_dec_ref(v___y_172_);
    crate::leanh::lean_dec(v___y_171_);
    crate::leanh::lean_dec_ref(v___y_170_);
    return v_res_175_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_177_ = l_Lean_Compiler_LCNF_getOtherDeclType___closed__0;
    v___x_178_ = l_Lean_stringToMessageData(v___x_177_);
    return v___x_178_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getOtherDeclType(
    mut v_declName_179_: *mut crate::leanh::LeanObject,
    mut v_us_180_: *mut crate::leanh::LeanObject,
    mut v_a_181_: *mut crate::leanh::LeanObject,
    mut v_a_182_: *mut crate::leanh::LeanObject,
    mut v_a_183_: *mut crate::leanh::LeanObject,
    mut v_a_184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: u8 = 0;
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_196_: u8 = 0;
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_186_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_181_);
                if crate::leanh::lean_obj_tag(v___x_186_) == 0 {
                    v_a_187_ = crate::leanh::lean_ctor_get(v___x_186_, 0);
                    crate::leanh::lean_inc(v_a_187_);
                    crate::leanh::lean_dec_ref_known(v___x_186_, 1);
                    v___x_188_ = (crate::leanh::lean_unbox(v_a_187_) as u8);
                    crate::leanh::lean_dec(v_a_187_);
                    match v___x_188_ {
                        0 => {
                            v___x_189_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(
                                v_declName_179_,
                                v_us_180_,
                                v_a_183_,
                                v_a_184_,
                            );
                            return v___x_189_;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_us_180_);
                            v___x_190_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(
                                v_declName_179_,
                                v_a_183_,
                                v_a_184_,
                            );
                            return v___x_190_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_us_180_);
                            crate::leanh::lean_dec(v_declName_179_);
                            v___x_191_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_getOtherDeclType___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_getOtherDeclType___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1,
                            );
                            v___x_192_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(v___x_191_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
                            return v___x_192_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_us_180_);
                    crate::leanh::lean_dec(v_declName_179_);
                    v_a_193_ = crate::leanh::lean_ctor_get(v___x_186_, 0);
                    v_isSharedCheck_200_ = (!crate::leanh::lean_is_exclusive(v___x_186_)) as u8;
                    if v_isSharedCheck_200_ == 0 {
                        v___x_195_ = v___x_186_;
                        v_isShared_196_ = v_isSharedCheck_200_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_193_);
                        crate::leanh::lean_dec(v___x_186_);
                        v___x_195_ = crate::leanh::lean_box(0);
                        v_isShared_196_ = v_isSharedCheck_200_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_196_ == 0 {
                    v___x_198_ = v___x_195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_199_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
                    v___x_198_ = v_reuseFailAlloc_199_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getOtherDeclType___boxed(
    mut v_declName_201_: *mut crate::leanh::LeanObject,
    mut v_us_202_: *mut crate::leanh::LeanObject,
    mut v_a_203_: *mut crate::leanh::LeanObject,
    mut v_a_204_: *mut crate::leanh::LeanObject,
    mut v_a_205_: *mut crate::leanh::LeanObject,
    mut v_a_206_: *mut crate::leanh::LeanObject,
    mut v_a_207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_208_ = l_Lean_Compiler_LCNF_getOtherDeclType(
        v_declName_201_,
        v_us_202_,
        v_a_203_,
        v_a_204_,
        v_a_205_,
        v_a_206_,
    );
    crate::leanh::lean_dec(v_a_206_);
    crate::leanh::lean_dec_ref(v_a_205_);
    crate::leanh::lean_dec(v_a_204_);
    crate::leanh::lean_dec_ref(v_a_203_);
    return v_res_208_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_OtherDecl(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_OtherDecl(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_OtherDecl(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
}
