// Lean compiler output
// Module: Lean.Compiler.LCNF.OtherDecl
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.MonoTypes Lean.Compiler.LCNF.ToImpureType
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
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getOtherDeclType___closed__0_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            103, 101, 116, 79, 116, 104, 101, 114, 68, 101, 99, 108, 84, 121, 112, 101, 32, 117,
            110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 102, 111, 114, 32, 105, 109, 112,
            117, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getOtherDeclType___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_getOtherDeclType___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_getOtherDeclType___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    v___x_105_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_105_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    v___x_106_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__0);
    v___x_107_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_107_, 0, v___x_106_);
    return v___x_107_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    v___x_108_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__1);
    v___x_109_ = lean_unsigned_to_nat(0);
    v___x_110_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_110_, 0, v___x_109_);
    lean_ctor_set(v___x_110_, 1, v___x_109_);
    lean_ctor_set(v___x_110_, 2, v___x_109_);
    lean_ctor_set(v___x_110_, 3, v___x_109_);
    lean_ctor_set(v___x_110_, 4, v___x_108_);
    lean_ctor_set(v___x_110_, 5, v___x_108_);
    lean_ctor_set(v___x_110_, 6, v___x_108_);
    lean_ctor_set(v___x_110_, 7, v___x_108_);
    lean_ctor_set(v___x_110_, 8, v___x_108_);
    lean_ctor_set(v___x_110_, 9, v___x_108_);
    return v___x_110_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(
    mut v_msg_111_: *mut LeanObject,
    mut v___y_112_: *mut LeanObject,
    mut v___y_113_: *mut LeanObject,
    mut v___y_114_: *mut LeanObject,
    mut v___y_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_125_: u8 = 0;
    let mut v_env_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_130_: u8 = 0;
    let mut v___x_131_: u8 = 0;
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_142_: u8 = 0;
    let mut v_unused_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_144_: u8 = 0;
    let mut v_a_145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_148_: u8 = 0;
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_117_ = lean_ctor_get(v___y_114_, 2);
                v_ref_118_ = lean_ctor_get(v___y_114_, 5);
                v___x_119_ = lean_st_ref_get(v___y_115_);
                v___x_120_ = lean_st_ref_get(v___y_113_);
                v___x_121_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_112_);
                if lean_obj_tag(v___x_121_) == 0 {
                    v_a_122_ = lean_ctor_get(v___x_121_, 0);
                    v_isSharedCheck_144_ = (!lean_is_exclusive(v___x_121_)) as u8;
                    if v_isSharedCheck_144_ == 0 {
                        v___x_124_ = v___x_121_;
                        v_isShared_125_ = v_isSharedCheck_144_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_122_);
                        lean_dec(v___x_121_);
                        v___x_124_ = lean_box(0);
                        v_isShared_125_ = v_isSharedCheck_144_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_120_);
                    lean_dec(v___x_119_);
                    lean_dec_ref(v_msg_111_);
                    v_a_145_ = lean_ctor_get(v___x_121_, 0);
                    v_isSharedCheck_152_ = (!lean_is_exclusive(v___x_121_)) as u8;
                    if v_isSharedCheck_152_ == 0 {
                        v___x_147_ = v___x_121_;
                        v_isShared_148_ = v_isSharedCheck_152_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_145_);
                        lean_dec(v___x_121_);
                        v___x_147_ = lean_box(0);
                        v_isShared_148_ = v_isSharedCheck_152_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_126_ = lean_ctor_get(v___x_119_, 0);
                lean_inc_ref(v_env_126_);
                lean_dec(v___x_119_);
                v_lctx_127_ = lean_ctor_get(v___x_120_, 0);
                v_isSharedCheck_142_ = (!lean_is_exclusive(v___x_120_)) as u8;
                if v_isSharedCheck_142_ == 0 {
                    v_unused_143_ = lean_ctor_get(v___x_120_, 1);
                    lean_dec(v_unused_143_);
                    v___x_129_ = v___x_120_;
                    v_isShared_130_ = v_isSharedCheck_142_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_127_);
                    lean_dec(v___x_120_);
                    v___x_129_ = lean_box(0);
                    v_isShared_130_ = v_isSharedCheck_142_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_131_ = (lean_unbox(v_a_122_) as u8);
                lean_dec(v_a_122_);
                v___x_132_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_127_, v___x_131_);
                lean_dec_ref(v_lctx_127_);
                v___x_133_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg___closed__2);
                lean_inc_ref(v_options_117_);
                v___x_134_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_134_, 0, v_env_126_);
                lean_ctor_set(v___x_134_, 1, v___x_133_);
                lean_ctor_set(v___x_134_, 2, v___x_132_);
                lean_ctor_set(v___x_134_, 3, v_options_117_);
                if v_isShared_130_ == 0 {
                    lean_ctor_set_tag(v___x_129_, 3);
                    lean_ctor_set(v___x_129_, 1, v_msg_111_);
                    lean_ctor_set(v___x_129_, 0, v___x_134_);
                    v___x_136_ = v___x_129_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_141_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_134_);
                    lean_ctor_set(v_reuseFailAlloc_141_, 1, v_msg_111_);
                    v___x_136_ = v_reuseFailAlloc_141_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_ref_118_);
                v___x_137_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_137_, 0, v_ref_118_);
                lean_ctor_set(v___x_137_, 1, v___x_136_);
                if v_isShared_125_ == 0 {
                    lean_ctor_set_tag(v___x_124_, 1);
                    lean_ctor_set(v___x_124_, 0, v___x_137_);
                    v___x_139_ = v___x_124_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
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
                    v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
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
    mut v_msg_153_: *mut LeanObject,
    mut v___y_154_: *mut LeanObject,
    mut v___y_155_: *mut LeanObject,
    mut v___y_156_: *mut LeanObject,
    mut v___y_157_: *mut LeanObject,
    mut v___y_158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_159_: *mut LeanObject = core::ptr::null_mut();
    v_res_159_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(
        v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_,
    );
    lean_dec(v___y_157_);
    lean_dec_ref(v___y_156_);
    lean_dec(v___y_155_);
    lean_dec_ref(v___y_154_);
    return v_res_159_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(
    mut v_00_u03b1_160_: *mut LeanObject,
    mut v_msg_161_: *mut LeanObject,
    mut v___y_162_: *mut LeanObject,
    mut v___y_163_: *mut LeanObject,
    mut v___y_164_: *mut LeanObject,
    mut v___y_165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    v___x_167_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___redArg(
        v_msg_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_,
    );
    return v___x_167_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0___boxed(
    mut v_00_u03b1_168_: *mut LeanObject,
    mut v_msg_169_: *mut LeanObject,
    mut v___y_170_: *mut LeanObject,
    mut v___y_171_: *mut LeanObject,
    mut v___y_172_: *mut LeanObject,
    mut v___y_173_: *mut LeanObject,
    mut v___y_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_175_: *mut LeanObject = core::ptr::null_mut();
    v_res_175_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getOtherDeclType_spec__0(
        v_00_u03b1_168_,
        v_msg_169_,
        v___y_170_,
        v___y_171_,
        v___y_172_,
        v___y_173_,
    );
    lean_dec(v___y_173_);
    lean_dec_ref(v___y_172_);
    lean_dec(v___y_171_);
    lean_dec_ref(v___y_170_);
    return v_res_175_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1() -> *mut LeanObject {
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    v___x_177_ = l_Lean_Compiler_LCNF_getOtherDeclType___closed__0;
    v___x_178_ = l_Lean_stringToMessageData(v___x_177_);
    return v___x_178_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getOtherDeclType(
    mut v_declName_179_: *mut LeanObject,
    mut v_us_180_: *mut LeanObject,
    mut v_a_181_: *mut LeanObject,
    mut v_a_182_: *mut LeanObject,
    mut v_a_183_: *mut LeanObject,
    mut v_a_184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: u8 = 0;
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_196_: u8 = 0;
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_186_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_181_);
                if lean_obj_tag(v___x_186_) == 0 {
                    v_a_187_ = lean_ctor_get(v___x_186_, 0);
                    lean_inc(v_a_187_);
                    lean_dec_ref_known(v___x_186_, 1);
                    v___x_188_ = (lean_unbox(v_a_187_) as u8);
                    lean_dec(v_a_187_);
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
                            lean_dec(v_us_180_);
                            v___x_190_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(
                                v_declName_179_,
                                v_a_183_,
                                v_a_184_,
                            );
                            return v___x_190_;
                        }
                        _ => {
                            lean_dec(v_us_180_);
                            lean_dec(v_declName_179_);
                            v___x_191_ = lean_obj_once(
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
                    lean_dec(v_us_180_);
                    lean_dec(v_declName_179_);
                    v_a_193_ = lean_ctor_get(v___x_186_, 0);
                    v_isSharedCheck_200_ = (!lean_is_exclusive(v___x_186_)) as u8;
                    if v_isSharedCheck_200_ == 0 {
                        v___x_195_ = v___x_186_;
                        v_isShared_196_ = v_isSharedCheck_200_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_193_);
                        lean_dec(v___x_186_);
                        v___x_195_ = lean_box(0);
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
                    v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
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
    mut v_declName_201_: *mut LeanObject,
    mut v_us_202_: *mut LeanObject,
    mut v_a_203_: *mut LeanObject,
    mut v_a_204_: *mut LeanObject,
    mut v_a_205_: *mut LeanObject,
    mut v_a_206_: *mut LeanObject,
    mut v_a_207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_208_: *mut LeanObject = core::ptr::null_mut();
    v_res_208_ = l_Lean_Compiler_LCNF_getOtherDeclType(
        v_declName_201_,
        v_us_202_,
        v_a_203_,
        v_a_204_,
        v_a_205_,
        v_a_206_,
    );
    lean_dec(v_a_206_);
    lean_dec_ref(v_a_205_);
    lean_dec(v_a_204_);
    lean_dec_ref(v_a_203_);
    return v_res_208_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_OtherDecl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_OtherDecl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_OtherDecl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
}
