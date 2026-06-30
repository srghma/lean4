// Lean compiler output
// Module: Lean.Language.Lean.Types
// Imports: Lean.Elab.Command
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity, lean_thunk_get_own};
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Language::Basic::{
    l_Lean_Language_SnapshotTask_finished___redArg, l_Lean_Language_SnapshotTask_map___redArg,
};
pub static l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__2 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__1
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__3
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Language_Lean_pushOpt___redArg(
    mut v_a_x3f_179_: *mut leanh::LeanObject,
    mut v_as_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_x3f_179_) == 0 {
        return v_as_180_;
    } else {
        let mut v_val_181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_181_ = leanh::lean_ctor_get(v_a_x3f_179_, 0);
        leanh::lean_inc(v_val_181_);
        leanh::lean_dec_ref_known(v_a_x3f_179_, 1);
        v___x_182_ = lean_array_push(v_as_180_, v_val_181_);
        return v___x_182_;
    }
}
pub unsafe fn l_Lean_Language_Lean_pushOpt(
    mut v_00_u03b1_183_: *mut leanh::LeanObject,
    mut v_a_x3f_184_: *mut leanh::LeanObject,
    mut v_as_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_186_ = l_Lean_Language_Lean_pushOpt___redArg(v_a_x3f_184_, v_as_185_);
    return v___x_186_;
}
pub unsafe fn l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0(
    mut v_s_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSnapshot_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_193_: u8 = 0;
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_198_: u8 = 0;
    let mut v_unused_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_190_ = leanh::lean_ctor_get(v_s_189_, 0);
                v_isSharedCheck_198_ = (!leanh::lean_is_exclusive(v_s_189_)) as u8;
                if v_isSharedCheck_198_ == 0 {
                    v_unused_199_ = leanh::lean_ctor_get(v_s_189_, 1);
                    leanh::lean_dec(v_unused_199_);
                    v___x_192_ = v_s_189_;
                    v_isShared_193_ = v_isSharedCheck_198_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toSnapshot_190_);
                    leanh::lean_dec(v_s_189_);
                    v___x_192_ = leanh::lean_box(0);
                    v_isShared_193_ = v_isSharedCheck_198_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_194_ = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0;
                if v_isShared_193_ == 0 {
                    leanh::lean_ctor_set(v___x_192_, 1, v___x_194_);
                    v___x_196_ = v___x_192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_197_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_197_, 0, v_toSnapshot_190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_194_);
                    v___x_196_ = v_reuseFailAlloc_197_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0(
    mut v_s_202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tree_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tree_203_ = leanh::lean_ctor_get(v_s_202_, 1);
    v___x_204_ = lean_thunk_get_own(v_tree_203_);
    return v___x_204_;
}
pub unsafe fn l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0___boxed(
    mut v_s_205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_206_ =
        l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0(v_s_205_);
    leanh::lean_dec_ref(v_s_205_);
    return v_res_206_;
}
pub unsafe fn l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__2(
    mut v_s_207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0;
    v___x_209_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_209_, 0, v_s_207_);
    leanh::lean_ctor_set(v___x_209_, 1, v___x_208_);
    return v___x_209_;
}
pub unsafe fn l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(
    mut v_s_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_elabSnap_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultSnap_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoTreeSnap_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportSnap_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: u8 = 0;
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_elabSnap_213_ = leanh::lean_ctor_get(v_s_212_, 1);
    leanh::lean_inc_ref(v_elabSnap_213_);
    v_resultSnap_214_ = leanh::lean_ctor_get(v_s_212_, 2);
    leanh::lean_inc_ref(v_resultSnap_214_);
    v_infoTreeSnap_215_ = leanh::lean_ctor_get(v_s_212_, 3);
    leanh::lean_inc_ref(v_infoTreeSnap_215_);
    v_toSnapshot_216_ = leanh::lean_ctor_get(v_s_212_, 0);
    leanh::lean_inc_ref(v_toSnapshot_216_);
    v_reportSnap_217_ = leanh::lean_ctor_get(v_s_212_, 4);
    leanh::lean_inc_ref(v_reportSnap_217_);
    leanh::lean_dec_ref(v_s_212_);
    v_stx_x3f_218_ = leanh::lean_ctor_get(v_elabSnap_213_, 0);
    leanh::lean_inc(v_stx_x3f_218_);
    v_reportingRange_219_ = leanh::lean_ctor_get(v_elabSnap_213_, 1);
    leanh::lean_inc(v_reportingRange_219_);
    v_stx_x3f_220_ = leanh::lean_ctor_get(v_resultSnap_214_, 0);
    leanh::lean_inc(v_stx_x3f_220_);
    v_reportingRange_221_ = leanh::lean_ctor_get(v_resultSnap_214_, 1);
    leanh::lean_inc(v_reportingRange_221_);
    v_stx_x3f_222_ = leanh::lean_ctor_get(v_infoTreeSnap_215_, 0);
    leanh::lean_inc(v_stx_x3f_222_);
    v_reportingRange_223_ = leanh::lean_ctor_get(v_infoTreeSnap_215_, 1);
    leanh::lean_inc(v_reportingRange_223_);
    v___f_224_ = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0;
    v___x_225_ = 1;
    v___x_226_ = l_Lean_Language_SnapshotTask_map___redArg(
        v_elabSnap_213_,
        v___f_224_,
        v_stx_x3f_218_,
        v_reportingRange_219_,
        v___x_225_,
    );
    v___f_227_ = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0;
    v___f_228_ = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1;
    v___x_229_ = l_Lean_Language_SnapshotTask_map___redArg(
        v_resultSnap_214_,
        v___f_227_,
        v_stx_x3f_220_,
        v_reportingRange_221_,
        v___x_225_,
    );
    v___x_230_ = l_Lean_Language_SnapshotTask_map___redArg(
        v_infoTreeSnap_215_,
        v___f_228_,
        v_stx_x3f_222_,
        v_reportingRange_223_,
        v___x_225_,
    );
    v___x_231_ = leanh::lean_unsigned_to_nat(4);
    v___x_232_ = lean_mk_empty_array_with_capacity(v___x_231_);
    v___x_233_ = lean_array_push(v___x_232_, v___x_226_);
    v___x_234_ = lean_array_push(v___x_233_, v___x_229_);
    v___x_235_ = lean_array_push(v___x_234_, v___x_230_);
    v___x_236_ = lean_array_push(v___x_235_, v_reportSnap_217_);
    v___x_237_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_237_, 0, v_toSnapshot_216_);
    leanh::lean_ctor_set(v___x_237_, 1, v___x_236_);
    return v___x_237_;
}
pub unsafe fn l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(
    mut v_s_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSnapshot_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCmdSnap_x3f_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_259_: u8 = 0;
    let mut v_stx_x3f_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: u8 = 0;
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_241_ = leanh::lean_ctor_get(v_s_240_, 0);
                leanh::lean_inc_ref(v_toSnapshot_241_);
                v_stx_242_ = leanh::lean_ctor_get(v_s_240_, 1);
                leanh::lean_inc(v_stx_242_);
                v_elabSnap_243_ = leanh::lean_ctor_get(v_s_240_, 3);
                leanh::lean_inc_ref(v_elabSnap_243_);
                v_nextCmdSnap_x3f_244_ = leanh::lean_ctor_get(v_s_240_, 4);
                leanh::lean_inc(v_nextCmdSnap_x3f_244_);
                leanh::lean_dec_ref(v_s_240_);
                if leanh::lean_obj_tag(v_nextCmdSnap_x3f_244_) == 0 {
                    v___x_255_ = leanh::lean_box(0);
                    v___y_246_ = v___x_255_;
                    state = 1;
                    continue;
                } else {
                    v_val_256_ = leanh::lean_ctor_get(v_nextCmdSnap_x3f_244_, 0);
                    v_isSharedCheck_268_ =
                        (!leanh::lean_is_exclusive(v_nextCmdSnap_x3f_244_)) as u8;
                    if v_isSharedCheck_268_ == 0 {
                        v___x_258_ = v_nextCmdSnap_x3f_244_;
                        v_isShared_259_ = v_isSharedCheck_268_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_256_);
                        leanh::lean_dec(v_nextCmdSnap_x3f_244_);
                        v___x_258_ = leanh::lean_box(0);
                        v_isShared_259_ = v_isSharedCheck_268_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_247_, 0, v_stx_242_);
                v___x_248_ = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(
                    v_elabSnap_243_,
                );
                v___x_249_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_247_, v___x_248_);
                v___x_250_ = leanh::lean_unsigned_to_nat(1);
                v___x_251_ = lean_mk_empty_array_with_capacity(v___x_250_);
                v___x_252_ = lean_array_push(v___x_251_, v___x_249_);
                v___x_253_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_246_, v___x_252_);
                v___x_254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_254_, 0, v_toSnapshot_241_);
                leanh::lean_ctor_set(v___x_254_, 1, v___x_253_);
                return v___x_254_;
            }
            2 => {
                v_stx_x3f_260_ = leanh::lean_ctor_get(v_val_256_, 0);
                leanh::lean_inc(v_stx_x3f_260_);
                v_reportingRange_261_ = leanh::lean_ctor_get(v_val_256_, 1);
                leanh::lean_inc(v_reportingRange_261_);
                v___x_262_ = leanh::lean_alloc_closure(
                    l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go
                        as *mut core::ffi::c_void,
                    1,
                    0,
                );
                v___x_263_ = 1;
                v___x_264_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_val_256_,
                    v___x_262_,
                    v_stx_x3f_260_,
                    v_reportingRange_261_,
                    v___x_263_,
                );
                if v_isShared_259_ == 0 {
                    leanh::lean_ctor_set(v___x_258_, 0, v___x_264_);
                    v___x_266_ = v___x_258_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_267_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
                    v___x_266_ = v_reuseFailAlloc_267_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_246_ = v___x_266_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(
    mut v___f_271_: *mut leanh::LeanObject,
    mut v_s_272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSnapshot_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: u8 = 0;
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_291_: u8 = 0;
    let mut v_firstCmdSnap_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: u8 = 0;
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_273_ = leanh::lean_ctor_get(v_s_272_, 0);
                leanh::lean_inc_ref(v_toSnapshot_273_);
                v_metaSnap_274_ = leanh::lean_ctor_get(v_s_272_, 1);
                leanh::lean_inc_ref(v_metaSnap_274_);
                v_result_x3f_275_ = leanh::lean_ctor_get(v_s_272_, 2);
                leanh::lean_inc(v_result_x3f_275_);
                leanh::lean_dec_ref(v_s_272_);
                if leanh::lean_obj_tag(v_result_x3f_275_) == 0 {
                    v___x_287_ = leanh::lean_box(0);
                    v___y_277_ = v___x_287_;
                    state = 1;
                    continue;
                } else {
                    v_val_288_ = leanh::lean_ctor_get(v_result_x3f_275_, 0);
                    v_isSharedCheck_301_ =
                        (!leanh::lean_is_exclusive(v_result_x3f_275_)) as u8;
                    if v_isSharedCheck_301_ == 0 {
                        v___x_290_ = v_result_x3f_275_;
                        v_isShared_291_ = v_isSharedCheck_301_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_288_);
                        leanh::lean_dec(v_result_x3f_275_);
                        v___x_290_ = leanh::lean_box(0);
                        v_isShared_291_ = v_isSharedCheck_301_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_x3f_278_ = leanh::lean_ctor_get(v_metaSnap_274_, 0);
                leanh::lean_inc(v_stx_x3f_278_);
                v_reportingRange_279_ = leanh::lean_ctor_get(v_metaSnap_274_, 1);
                leanh::lean_inc(v_reportingRange_279_);
                v___x_280_ = 1;
                v___x_281_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_274_,
                    v___f_271_,
                    v_stx_x3f_278_,
                    v_reportingRange_279_,
                    v___x_280_,
                );
                v___x_282_ = leanh::lean_unsigned_to_nat(1);
                v___x_283_ = lean_mk_empty_array_with_capacity(v___x_282_);
                v___x_284_ = lean_array_push(v___x_283_, v___x_281_);
                v___x_285_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_277_, v___x_284_);
                v___x_286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_286_, 0, v_toSnapshot_273_);
                leanh::lean_ctor_set(v___x_286_, 1, v___x_285_);
                return v___x_286_;
            }
            2 => {
                v_firstCmdSnap_292_ = leanh::lean_ctor_get(v_val_288_, 1);
                leanh::lean_inc_ref(v_firstCmdSnap_292_);
                leanh::lean_dec(v_val_288_);
                v_stx_x3f_293_ = leanh::lean_ctor_get(v_firstCmdSnap_292_, 0);
                leanh::lean_inc(v_stx_x3f_293_);
                v_reportingRange_294_ = leanh::lean_ctor_get(v_firstCmdSnap_292_, 1);
                leanh::lean_inc(v_reportingRange_294_);
                v___x_295_ =
                    l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0;
                v___x_296_ = 1;
                v___x_297_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_firstCmdSnap_292_,
                    v___x_295_,
                    v_stx_x3f_293_,
                    v_reportingRange_294_,
                    v___x_296_,
                );
                if v_isShared_291_ == 0 {
                    leanh::lean_ctor_set(v___x_290_, 0, v___x_297_);
                    v___x_299_ = v___x_290_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_300_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
                    v___x_299_ = v_reuseFailAlloc_300_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_277_ = v___x_299_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__3(
    mut v___f_305_: *mut leanh::LeanObject,
    mut v___f_306_: *mut leanh::LeanObject,
    mut v_s_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSnapshot_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: u8 = 0;
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_326_: u8 = 0;
    let mut v_processedSnap_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: u8 = 0;
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_308_ = leanh::lean_ctor_get(v_s_307_, 0);
                leanh::lean_inc_ref(v_toSnapshot_308_);
                v_metaSnap_309_ = leanh::lean_ctor_get(v_s_307_, 1);
                leanh::lean_inc_ref(v_metaSnap_309_);
                v_result_x3f_310_ = leanh::lean_ctor_get(v_s_307_, 4);
                leanh::lean_inc(v_result_x3f_310_);
                leanh::lean_dec_ref(v_s_307_);
                if leanh::lean_obj_tag(v_result_x3f_310_) == 0 {
                    leanh::lean_dec_ref(v___f_306_);
                    v___x_322_ = leanh::lean_box(0);
                    v___y_312_ = v___x_322_;
                    state = 1;
                    continue;
                } else {
                    v_val_323_ = leanh::lean_ctor_get(v_result_x3f_310_, 0);
                    v_isSharedCheck_335_ =
                        (!leanh::lean_is_exclusive(v_result_x3f_310_)) as u8;
                    if v_isSharedCheck_335_ == 0 {
                        v___x_325_ = v_result_x3f_310_;
                        v_isShared_326_ = v_isSharedCheck_335_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_323_);
                        leanh::lean_dec(v_result_x3f_310_);
                        v___x_325_ = leanh::lean_box(0);
                        v_isShared_326_ = v_isSharedCheck_335_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_x3f_313_ = leanh::lean_ctor_get(v_metaSnap_309_, 0);
                leanh::lean_inc(v_stx_x3f_313_);
                v_reportingRange_314_ = leanh::lean_ctor_get(v_metaSnap_309_, 1);
                leanh::lean_inc(v_reportingRange_314_);
                v___x_315_ = 1;
                v___x_316_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_309_,
                    v___f_305_,
                    v_stx_x3f_313_,
                    v_reportingRange_314_,
                    v___x_315_,
                );
                v___x_317_ = leanh::lean_unsigned_to_nat(1);
                v___x_318_ = lean_mk_empty_array_with_capacity(v___x_317_);
                v___x_319_ = lean_array_push(v___x_318_, v___x_316_);
                v___x_320_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_312_, v___x_319_);
                v___x_321_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_321_, 0, v_toSnapshot_308_);
                leanh::lean_ctor_set(v___x_321_, 1, v___x_320_);
                return v___x_321_;
            }
            2 => {
                v_processedSnap_327_ = leanh::lean_ctor_get(v_val_323_, 1);
                leanh::lean_inc_ref(v_processedSnap_327_);
                leanh::lean_dec(v_val_323_);
                v_stx_x3f_328_ = leanh::lean_ctor_get(v_processedSnap_327_, 0);
                leanh::lean_inc(v_stx_x3f_328_);
                v_reportingRange_329_ = leanh::lean_ctor_get(v_processedSnap_327_, 1);
                leanh::lean_inc(v_reportingRange_329_);
                v___x_330_ = 1;
                v___x_331_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_processedSnap_327_,
                    v___f_306_,
                    v_stx_x3f_328_,
                    v_reportingRange_329_,
                    v___x_330_,
                );
                if v_isShared_326_ == 0 {
                    leanh::lean_ctor_set(v___x_325_, 0, v___x_331_);
                    v___x_333_ = v___x_325_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
                    v___x_333_ = v_reuseFailAlloc_334_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_312_ = v___x_333_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(
    mut v_x_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_x3f_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_result_x3f_341_ = leanh::lean_ctor_get(v_x_340_, 2);
    leanh::lean_inc(v_result_x3f_341_);
    return v_result_x3f_341_;
}
pub unsafe fn l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed(
    mut v_x_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(v_x_342_);
    leanh::lean_dec_ref(v_x_342_);
    return v_res_343_;
}
pub unsafe fn _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ = leanh::lean_box(0);
    v___x_345_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_344_, v___x_344_);
    return v___x_345_;
}
pub unsafe fn l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(
    mut v_snap_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_x3f_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_result_x3f_348_ = leanh::lean_ctor_get(v_snap_347_, 4);
    leanh::lean_inc(v_result_x3f_348_);
    leanh::lean_dec_ref(v_snap_347_);
    if leanh::lean_obj_tag(v_result_x3f_348_) == 0 {
        let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_349_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0_once
            ),
            _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0,
        );
        return v___x_349_;
    } else {
        let mut v_val_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_processedSnap_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_x3f_352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_reportingRange_353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_355_: u8 = 0;
        let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_350_ = leanh::lean_ctor_get(v_result_x3f_348_, 0);
        leanh::lean_inc(v_val_350_);
        leanh::lean_dec_ref_known(v_result_x3f_348_, 1);
        v_processedSnap_351_ = leanh::lean_ctor_get(v_val_350_, 1);
        leanh::lean_inc_ref(v_processedSnap_351_);
        leanh::lean_dec(v_val_350_);
        v_stx_x3f_352_ = leanh::lean_ctor_get(v_processedSnap_351_, 0);
        leanh::lean_inc(v_stx_x3f_352_);
        v_reportingRange_353_ = leanh::lean_ctor_get(v_processedSnap_351_, 1);
        leanh::lean_inc(v_reportingRange_353_);
        v___f_354_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1;
        v___x_355_ = 1;
        v___x_356_ = l_Lean_Language_SnapshotTask_map___redArg(
            v_processedSnap_351_,
            v___f_354_,
            v_stx_x3f_352_,
            v_reportingRange_353_,
            v___x_355_,
        );
        return v___x_356_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Language_Lean_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Language_Lean_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Language_Lean_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Language_Lean_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Language_Lean_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Language_Lean_Types(builtin);
}