// Lean compiler output
// Module: Lean.Server.Snapshots
// Imports: Lean.Elab.Import Lean.Elab.Command Lean.Widget.InteractiveDiagnostic
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getPos_x3f, l_Lean_firstFrontendMacroScope};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_liftCoreM___boxed,
    l_Lean_Elab_Command_liftTermElabM___boxed, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Import::{
    initialize_Lean_Elab_Import, runtime_initialize_Lean_Elab_Import,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_InfoState_substituteLazy;
use crate::r#gen::Lean::Elab::InfoTree::Types::l_Lean_Elab_instInhabitedInfoTree_default;
use crate::r#gen::Lean::Parser::Module::l_Lean_Parser_isTerminalCommand;
use crate::r#gen::Lean::Widget::InteractiveDiagnostic::{
    initialize_Lean_Widget_InteractiveDiagnostic,
    runtime_initialize_Lean_Widget_InteractiveDiagnostic,
};
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_eq, lean_nat_dec_lt, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get};
pub static l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 83, 110, 97, 112, 115, 104, 111,
        116, 115, 0,
    ],
};
static mut l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 83, 110, 97, 112, 115, 104, 111,
        116, 115, 46, 83, 110, 97, 112, 115, 104, 111, 116, 46, 105, 110, 102, 111, 84, 114, 101,
        101, 0,
    ],
};
static mut l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 105, 110, 102, 111, 83, 116, 97, 116, 101, 46, 116, 114, 101, 101, 115, 46, 115,
        105, 122, 101, 32, 61, 61, 32, 49, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_endPos(
    mut v_s_143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mpState_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mpState_144_ = crate::leanh::lean_ctor_get(v_s_143_, 1);
    v_pos_145_ = crate::leanh::lean_ctor_get(v_mpState_144_, 0);
    crate::leanh::lean_inc(v_pos_145_);
    return v_pos_145_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_endPos___boxed(
    mut v_s_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_146_);
    crate::leanh::lean_dec_ref(v_s_146_);
    return v_res_147_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_env(
    mut v_s_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cmdState_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cmdState_149_ = crate::leanh::lean_ctor_get(v_s_148_, 2);
    v_env_150_ = crate::leanh::lean_ctor_get(v_cmdState_149_, 0);
    crate::leanh::lean_inc_ref(v_env_150_);
    return v_env_150_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_env___boxed(
    mut v_s_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_151_);
    crate::leanh::lean_dec_ref(v_s_151_);
    return v_res_152_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_msgLog(
    mut v_s_153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cmdState_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cmdState_154_ = crate::leanh::lean_ctor_get(v_s_153_, 2);
    v_messages_155_ = crate::leanh::lean_ctor_get(v_cmdState_154_, 1);
    crate::leanh::lean_inc_ref(v_messages_155_);
    return v_messages_155_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(
    mut v_s_156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_157_ = l_Lean_Server_Snapshots_Snapshot_msgLog(v_s_156_);
    crate::leanh::lean_dec_ref(v_s_156_);
    return v_res_157_;
}
pub unsafe fn l_panic___at___00Lean_Server_Snapshots_Snapshot_infoTree_spec__0(
    mut v_msg_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_159_ = l_Lean_Elab_instInhabitedInfoTree_default;
    v___x_160_ = lean_panic_fn_borrowed(v___x_159_, v_msg_158_);
    return v___x_160_;
}
pub unsafe fn _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_164_ = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2;
    v___x_165_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_166_ = crate::leanh::lean_unsigned_to_nat(48);
    v___x_167_ = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1;
    v___x_168_ = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0;
    v___x_169_ =
        l_mkPanicMessageWithDecl(v___x_168_, v___x_167_, v___x_166_, v___x_165_, v___x_164_);
    return v___x_169_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_infoTree(
    mut v_s_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cmdState_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: u8 = 0;
    v_cmdState_171_ = crate::leanh::lean_ctor_get(v_s_170_, 2);
    crate::leanh::lean_inc_ref(v_cmdState_171_);
    crate::leanh::lean_dec_ref(v_s_170_);
    v_infoState_172_ = crate::leanh::lean_ctor_get(v_cmdState_171_, 8);
    crate::leanh::lean_inc_ref(v_infoState_172_);
    crate::leanh::lean_dec_ref(v_cmdState_171_);
    v___x_173_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_172_);
    v_infoState_174_ = lean_task_get_own(v___x_173_);
    v_trees_175_ = crate::leanh::lean_ctor_get(v_infoState_174_, 2);
    crate::leanh::lean_inc_ref(v_trees_175_);
    crate::leanh::lean_dec(v_infoState_174_);
    v_size_176_ = crate::leanh::lean_ctor_get(v_trees_175_, 2);
    v___x_177_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_178_ = lean_nat_dec_eq(v_size_176_, v___x_177_);
    if v___x_178_ == 0 {
        let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_trees_175_);
        v___x_179_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3_once),
            _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3,
        );
        v___x_180_ = l_panic___at___00Lean_Server_Snapshots_Snapshot_infoTree_spec__0(v___x_179_);
        return v___x_180_;
    } else {
        let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_183_: u8 = 0;
        v___x_181_ = l_Lean_Elab_instInhabitedInfoTree_default;
        v___x_182_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_183_ = lean_nat_dec_lt(v___x_182_, v_size_176_);
        if v___x_183_ == 0 {
            let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_trees_175_);
            v___x_184_ = l_outOfBounds___redArg(v___x_181_);
            return v___x_184_;
        } else {
            let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_185_ =
                l_Lean_PersistentArray_get_x21___redArg(v___x_181_, v_trees_175_, v___x_182_);
            crate::leanh::lean_dec_ref(v_trees_175_);
            return v___x_185_;
        }
    }
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_isAtEnd(
    mut v_s_186_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_stx_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: u8 = 0;
    v_stx_187_ = crate::leanh::lean_ctor_get(v_s_186_, 0);
    crate::leanh::lean_inc(v_stx_187_);
    crate::leanh::lean_dec_ref(v_s_186_);
    v___x_188_ = l_Lean_Parser_isTerminalCommand(v_stx_187_);
    return v___x_188_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(
    mut v_s_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_190_: u8 = 0;
    let mut v_r_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_190_ = l_Lean_Server_Snapshots_Snapshot_isAtEnd(v_s_189_);
    v_r_191_ = crate::leanh::lean_box((v_res_190_) as usize);
    return v_r_191_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(
    mut v_snap_192_: *mut crate::leanh::LeanObject,
    mut v_doc_193_: *mut crate::leanh::LeanObject,
    mut v_c_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdState_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: u8 = 0;
    let mut v___y_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_214_: u8 = 0;
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_219_: u8 = 0;
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_196_ = crate::leanh::lean_ctor_get(v_doc_193_, 0);
                v_text_197_ = crate::leanh::lean_ctor_get(v_doc_193_, 3);
                v_stx_198_ = crate::leanh::lean_ctor_get(v_snap_192_, 0);
                crate::leanh::lean_inc(v_stx_198_);
                v_cmdState_199_ = crate::leanh::lean_ctor_get(v_snap_192_, 2);
                crate::leanh::lean_inc_ref(v_cmdState_199_);
                crate::leanh::lean_dec_ref(v_snap_192_);
                v___x_200_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_201_ = 0;
                v___x_220_ = l_Lean_Syntax_getPos_x3f(v_stx_198_, v___x_201_);
                crate::leanh::lean_dec(v_stx_198_);
                if crate::leanh::lean_obj_tag(v___x_220_) == 0 {
                    v___y_203_ = v___x_200_;
                    state = 1;
                    continue;
                } else {
                    v_val_221_ = crate::leanh::lean_ctor_get(v___x_220_, 0);
                    crate::leanh::lean_inc(v_val_221_);
                    crate::leanh::lean_dec_ref_known(v___x_220_, 1);
                    v___y_203_ = v_val_221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_204_ = lean_st_mk_ref(v_cmdState_199_);
                v___x_205_ = crate::leanh::lean_box(0);
                v___x_206_ = crate::leanh::lean_box(0);
                v___x_207_ = l_Lean_firstFrontendMacroScope;
                v___x_208_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_text_197_);
                crate::leanh::lean_inc_ref(v_uri_196_);
                v_ctx_209_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                crate::leanh::lean_ctor_set(v_ctx_209_, 0, v_uri_196_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 1, v_text_197_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 2, v___x_200_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 3, v___y_203_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 4, v___x_205_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 5, v___x_206_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 6, v___x_207_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 7, v___x_208_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 8, v___x_206_);
                crate::leanh::lean_ctor_set(v_ctx_209_, 9, v___x_206_);
                crate::leanh::lean_ctor_set_uint8(
                    v_ctx_209_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    v___x_201_,
                );
                crate::leanh::lean_inc(v___x_204_);
                v___x_210_ = crate::leanh::lean_apply_3(
                    v_c_194_,
                    v_ctx_209_,
                    v___x_204_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_210_) == 0 {
                    v_a_211_ = crate::leanh::lean_ctor_get(v___x_210_, 0);
                    v_isSharedCheck_219_ = (!crate::leanh::lean_is_exclusive(v___x_210_)) as u8;
                    if v_isSharedCheck_219_ == 0 {
                        v___x_213_ = v___x_210_;
                        v_isShared_214_ = v_isSharedCheck_219_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_211_);
                        crate::leanh::lean_dec(v___x_210_);
                        v___x_213_ = crate::leanh::lean_box(0);
                        v_isShared_214_ = v_isSharedCheck_219_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_204_);
                    return v___x_210_;
                }
            }
            2 => {
                v___x_215_ = lean_st_ref_get(v___x_204_);
                crate::leanh::lean_dec(v___x_204_);
                crate::leanh::lean_dec(v___x_215_);
                if v_isShared_214_ == 0 {
                    v___x_217_ = v___x_213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_218_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_211_);
                    v___x_217_ = v_reuseFailAlloc_218_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg___boxed(
    mut v_snap_222_: *mut crate::leanh::LeanObject,
    mut v_doc_223_: *mut crate::leanh::LeanObject,
    mut v_c_224_: *mut crate::leanh::LeanObject,
    mut v_a_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_226_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(
        v_snap_222_,
        v_doc_223_,
        v_c_224_,
    );
    crate::leanh::lean_dec_ref(v_doc_223_);
    return v_res_226_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runCommandElabM(
    mut v_00_u03b1_227_: *mut crate::leanh::LeanObject,
    mut v_snap_228_: *mut crate::leanh::LeanObject,
    mut v_doc_229_: *mut crate::leanh::LeanObject,
    mut v_c_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_232_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(
        v_snap_228_,
        v_doc_229_,
        v_c_230_,
    );
    return v___x_232_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runCommandElabM___boxed(
    mut v_00_u03b1_233_: *mut crate::leanh::LeanObject,
    mut v_snap_234_: *mut crate::leanh::LeanObject,
    mut v_doc_235_: *mut crate::leanh::LeanObject,
    mut v_c_236_: *mut crate::leanh::LeanObject,
    mut v_a_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_238_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM(
        v_00_u03b1_233_,
        v_snap_234_,
        v_doc_235_,
        v_c_236_,
    );
    crate::leanh::lean_dec_ref(v_doc_235_);
    return v_res_238_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(
    mut v_snap_239_: *mut crate::leanh::LeanObject,
    mut v_doc_240_: *mut crate::leanh::LeanObject,
    mut v_c_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_243_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_liftCoreM___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___x_243_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_243_, 1, v_c_241_);
    v___x_244_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(
        v_snap_239_,
        v_doc_240_,
        v___x_243_,
    );
    return v___x_244_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg___boxed(
    mut v_snap_245_: *mut crate::leanh::LeanObject,
    mut v_doc_246_: *mut crate::leanh::LeanObject,
    mut v_c_247_: *mut crate::leanh::LeanObject,
    mut v_a_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_249_ =
        l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_245_, v_doc_246_, v_c_247_);
    crate::leanh::lean_dec_ref(v_doc_246_);
    return v_res_249_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runCoreM(
    mut v_00_u03b1_250_: *mut crate::leanh::LeanObject,
    mut v_snap_251_: *mut crate::leanh::LeanObject,
    mut v_doc_252_: *mut crate::leanh::LeanObject,
    mut v_c_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ =
        l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_251_, v_doc_252_, v_c_253_);
    return v___x_255_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runCoreM___boxed(
    mut v_00_u03b1_256_: *mut crate::leanh::LeanObject,
    mut v_snap_257_: *mut crate::leanh::LeanObject,
    mut v_doc_258_: *mut crate::leanh::LeanObject,
    mut v_c_259_: *mut crate::leanh::LeanObject,
    mut v_a_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Lean_Server_Snapshots_Snapshot_runCoreM(
        v_00_u03b1_256_,
        v_snap_257_,
        v_doc_258_,
        v_c_259_,
    );
    crate::leanh::lean_dec_ref(v_doc_258_);
    return v_res_261_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(
    mut v_snap_262_: *mut crate::leanh::LeanObject,
    mut v_doc_263_: *mut crate::leanh::LeanObject,
    mut v_c_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_liftTermElabM___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___x_266_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_266_, 1, v_c_264_);
    v___x_267_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(
        v_snap_262_,
        v_doc_263_,
        v___x_266_,
    );
    return v___x_267_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg___boxed(
    mut v_snap_268_: *mut crate::leanh::LeanObject,
    mut v_doc_269_: *mut crate::leanh::LeanObject,
    mut v_c_270_: *mut crate::leanh::LeanObject,
    mut v_a_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_272_ =
        l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_268_, v_doc_269_, v_c_270_);
    crate::leanh::lean_dec_ref(v_doc_269_);
    return v_res_272_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runTermElabM(
    mut v_00_u03b1_273_: *mut crate::leanh::LeanObject,
    mut v_snap_274_: *mut crate::leanh::LeanObject,
    mut v_doc_275_: *mut crate::leanh::LeanObject,
    mut v_c_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_278_ =
        l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_274_, v_doc_275_, v_c_276_);
    return v___x_278_;
}
pub unsafe fn l_Lean_Server_Snapshots_Snapshot_runTermElabM___boxed(
    mut v_00_u03b1_279_: *mut crate::leanh::LeanObject,
    mut v_snap_280_: *mut crate::leanh::LeanObject,
    mut v_doc_281_: *mut crate::leanh::LeanObject,
    mut v_c_282_: *mut crate::leanh::LeanObject,
    mut v_a_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_284_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM(
        v_00_u03b1_279_,
        v_snap_280_,
        v_doc_281_,
        v_c_282_,
    );
    crate::leanh::lean_dec_ref(v_doc_281_);
    return v_res_284_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Snapshots(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Import(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_InteractiveDiagnostic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Snapshots(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Snapshots(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Import(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Widget_InteractiveDiagnostic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Snapshots(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Snapshots(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Snapshots(builtin);
}
