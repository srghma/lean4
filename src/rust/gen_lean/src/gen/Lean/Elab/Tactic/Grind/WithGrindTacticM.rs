// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.WithGrindTacticM
// Imports: Lean.Elab.Tactic.Grind.Basic Lean.Elab.Command
use crate::ffi::{lean_mk_array, lean_st_ref_get};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_liftTermElabM___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Basic::{
    initialize_Lean_Elab_Tactic_Grind_Basic, l_Lean_Elab_Tactic_Grind_GrindTacticM_run___redArg,
    runtime_initialize_Lean_Elab_Tactic_Grind_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    l_Lean_Meta_Grind_GrindM_run___redArg, l_Lean_Meta_Grind_mkDefaultParams,
};
pub static l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 83, 105, 109, 112, 0,
    ],
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        3814902364570594393 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0_value:
    leanh::LeanCtorObject<17> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 13
            + 32) as u16,
        other: 13,
        tag: 0,
    },
    m_objs: [
        (((9 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((5 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((8 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((8 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((100000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1048576 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((10 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        72340168526266368 as *mut leanh::LeanObject,
        72340172821299200 as *mut leanh::LeanObject,
        72340172838076417 as *mut leanh::LeanObject,
        72339073326448897 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_168_;
}
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_169_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2,
    );
    v___x_170_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_170_, 0, v___x_169_);
    return v___x_170_;
}
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_171_ = leanh::lean_box(0);
    v___x_172_ = leanh::lean_unsigned_to_nat(16);
    v___x_173_ = lean_mk_array(v___x_172_, v___x_171_);
    return v___x_173_;
}
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_174_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4,
    );
    v___x_175_ = leanh::lean_unsigned_to_nat(0);
    v___x_176_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_176_, 0, v___x_175_);
    leanh::lean_ctor_set(v___x_176_, 1, v___x_174_);
    return v___x_176_;
}
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_177_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5,
    );
    v___x_178_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3,
    );
    v___x_179_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_179_, 0, v___x_178_);
    leanh::lean_ctor_set(v___x_179_, 1, v___x_178_);
    leanh::lean_ctor_set(v___x_179_, 2, v___x_177_);
    leanh::lean_ctor_set(v___x_179_, 3, v___x_177_);
    return v___x_179_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(
    mut v___x_180_: u8,
    mut v_a_181_: *mut leanh::LeanObject,
    mut v___x_182_: u8,
    mut v___y_183_: *mut leanh::LeanObject,
    mut v___y_184_: *mut leanh::LeanObject,
    mut v___y_185_: *mut leanh::LeanObject,
    mut v___y_186_: *mut leanh::LeanObject,
    mut v___y_187_: *mut leanh::LeanObject,
    mut v___y_188_: *mut leanh::LeanObject,
    mut v___y_189_: *mut leanh::LeanObject,
    mut v___y_190_: *mut leanh::LeanObject,
    mut v___y_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_193_ = lean_st_ref_get(v___y_185_);
    v___x_194_ = lean_st_ref_get(v___y_187_);
    v___x_195_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1;
    v___x_196_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_196_, 0, v___x_195_);
    leanh::lean_ctor_set_uint8(
        v___x_196_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_180_,
    );
    leanh::lean_inc(v___y_183_);
    leanh::lean_inc_ref(v___y_186_);
    leanh::lean_inc_ref(v___y_184_);
    v___x_197_ = leanh::lean_alloc_ctor(0, 5, (1) as u32);
    leanh::lean_ctor_set(v___x_197_, 0, v___x_196_);
    leanh::lean_ctor_set(v___x_197_, 1, v___y_184_);
    leanh::lean_ctor_set(v___x_197_, 2, v___y_186_);
    leanh::lean_ctor_set(v___x_197_, 3, v___y_183_);
    leanh::lean_ctor_set(v___x_197_, 4, v_a_181_);
    leanh::lean_ctor_set_uint8(
        v___x_197_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        v___x_182_,
    );
    v___x_198_ = leanh::lean_box(0);
    v___x_199_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6,
    );
    v___x_200_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_200_, 0, v___x_194_);
    leanh::lean_ctor_set(v___x_200_, 1, v___x_193_);
    leanh::lean_ctor_set(v___x_200_, 2, v___x_198_);
    leanh::lean_ctor_set(v___x_200_, 3, v___x_199_);
    v___x_201_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_201_, 0, v___x_197_);
    leanh::lean_ctor_set(v___x_201_, 1, v___x_200_);
    v___x_202_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_202_, 0, v___x_201_);
    return v___x_202_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed(
    mut v___x_203_: *mut leanh::LeanObject,
    mut v_a_204_: *mut leanh::LeanObject,
    mut v___x_205_: *mut leanh::LeanObject,
    mut v___y_206_: *mut leanh::LeanObject,
    mut v___y_207_: *mut leanh::LeanObject,
    mut v___y_208_: *mut leanh::LeanObject,
    mut v___y_209_: *mut leanh::LeanObject,
    mut v___y_210_: *mut leanh::LeanObject,
    mut v___y_211_: *mut leanh::LeanObject,
    mut v___y_212_: *mut leanh::LeanObject,
    mut v___y_213_: *mut leanh::LeanObject,
    mut v___y_214_: *mut leanh::LeanObject,
    mut v___y_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8495__boxed_216_: u8 = 0;
    let mut v___x_8497__boxed_217_: u8 = 0;
    let mut v_res_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8495__boxed_216_ = (leanh::lean_unbox(v___x_203_) as u8);
    v___x_8497__boxed_217_ = (leanh::lean_unbox(v___x_205_) as u8);
    v_res_218_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(
        v___x_8495__boxed_216_,
        v_a_204_,
        v___x_8497__boxed_217_,
        v___y_206_,
        v___y_207_,
        v___y_208_,
        v___y_209_,
        v___y_210_,
        v___y_211_,
        v___y_212_,
        v___y_213_,
        v___y_214_,
    );
    leanh::lean_dec(v___y_214_);
    leanh::lean_dec_ref(v___y_213_);
    leanh::lean_dec(v___y_212_);
    leanh::lean_dec_ref(v___y_211_);
    leanh::lean_dec(v___y_210_);
    leanh::lean_dec_ref(v___y_209_);
    leanh::lean_dec(v___y_208_);
    leanh::lean_dec_ref(v___y_207_);
    leanh::lean_dec(v___y_206_);
    return v_res_218_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(
    mut v___x_219_: *mut leanh::LeanObject,
    mut v___x_220_: u8,
    mut v___x_221_: u8,
    mut v_k_222_: *mut leanh::LeanObject,
    mut v___y_223_: *mut leanh::LeanObject,
    mut v___y_224_: *mut leanh::LeanObject,
    mut v___y_225_: *mut leanh::LeanObject,
    mut v___y_226_: *mut leanh::LeanObject,
    mut v___y_227_: *mut leanh::LeanObject,
    mut v___y_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v_fst_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_249_: u8 = 0;
    let mut v_a_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_253_: u8 = 0;
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_257_: u8 = 0;
    let mut v_a_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_261_: u8 = 0;
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_265_: u8 = 0;
    let mut v_a_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_269_: u8 = 0;
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_230_ = l_Lean_Meta_Grind_mkDefaultParams(
                    v___x_219_, v___y_225_, v___y_226_, v___y_227_, v___y_228_,
                );
                if leanh::lean_obj_tag(v___x_230_) == 0 {
                    v_a_231_ = leanh::lean_ctor_get(v___x_230_, 0);
                    leanh::lean_inc_n(v_a_231_, 2);
                    leanh::lean_dec_ref_known(v___x_230_, 1);
                    v___x_232_ = leanh::lean_box((v___x_220_) as usize);
                    v___x_233_ = leanh::lean_box((v___x_221_) as usize);
                    v___f_234_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        13,
                        3,
                    );
                    leanh::lean_closure_set(v___f_234_, 0, v___x_232_);
                    leanh::lean_closure_set(v___f_234_, 1, v_a_231_);
                    leanh::lean_closure_set(v___f_234_, 2, v___x_233_);
                    v___x_235_ = leanh::lean_box(0);
                    v___x_236_ = l_Lean_Meta_Grind_GrindM_run___redArg(
                        v___f_234_, v_a_231_, v___x_235_, v___y_225_, v___y_226_, v___y_227_,
                        v___y_228_,
                    );
                    if leanh::lean_obj_tag(v___x_236_) == 0 {
                        v_a_237_ = leanh::lean_ctor_get(v___x_236_, 0);
                        leanh::lean_inc(v_a_237_);
                        leanh::lean_dec_ref_known(v___x_236_, 1);
                        v_fst_238_ = leanh::lean_ctor_get(v_a_237_, 0);
                        leanh::lean_inc(v_fst_238_);
                        v_snd_239_ = leanh::lean_ctor_get(v_a_237_, 1);
                        leanh::lean_inc(v_snd_239_);
                        leanh::lean_dec(v_a_237_);
                        v___x_240_ = l_Lean_Elab_Tactic_Grind_GrindTacticM_run___redArg(
                            v_k_222_, v_fst_238_, v_snd_239_, v___y_223_, v___y_224_, v___y_225_,
                            v___y_226_, v___y_227_, v___y_228_,
                        );
                        if leanh::lean_obj_tag(v___x_240_) == 0 {
                            v_a_241_ = leanh::lean_ctor_get(v___x_240_, 0);
                            v_isSharedCheck_249_ =
                                (!leanh::lean_is_exclusive(v___x_240_)) as u8;
                            if v_isSharedCheck_249_ == 0 {
                                v___x_243_ = v___x_240_;
                                v_isShared_244_ = v_isSharedCheck_249_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_241_);
                                leanh::lean_dec(v___x_240_);
                                v___x_243_ = leanh::lean_box(0);
                                v_isShared_244_ = v_isSharedCheck_249_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_250_ = leanh::lean_ctor_get(v___x_240_, 0);
                            v_isSharedCheck_257_ =
                                (!leanh::lean_is_exclusive(v___x_240_)) as u8;
                            if v_isSharedCheck_257_ == 0 {
                                v___x_252_ = v___x_240_;
                                v_isShared_253_ = v_isSharedCheck_257_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_250_);
                                leanh::lean_dec(v___x_240_);
                                v___x_252_ = leanh::lean_box(0);
                                v_isShared_253_ = v_isSharedCheck_257_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_k_222_);
                        v_a_258_ = leanh::lean_ctor_get(v___x_236_, 0);
                        v_isSharedCheck_265_ = (!leanh::lean_is_exclusive(v___x_236_)) as u8;
                        if v_isSharedCheck_265_ == 0 {
                            v___x_260_ = v___x_236_;
                            v_isShared_261_ = v_isSharedCheck_265_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_258_);
                            leanh::lean_dec(v___x_236_);
                            v___x_260_ = leanh::lean_box(0);
                            v_isShared_261_ = v_isSharedCheck_265_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_k_222_);
                    v_a_266_ = leanh::lean_ctor_get(v___x_230_, 0);
                    v_isSharedCheck_273_ = (!leanh::lean_is_exclusive(v___x_230_)) as u8;
                    if v_isSharedCheck_273_ == 0 {
                        v___x_268_ = v___x_230_;
                        v_isShared_269_ = v_isSharedCheck_273_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_266_);
                        leanh::lean_dec(v___x_230_);
                        v___x_268_ = leanh::lean_box(0);
                        v_isShared_269_ = v_isSharedCheck_273_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_245_ = leanh::lean_ctor_get(v_a_241_, 0);
                leanh::lean_inc(v_fst_245_);
                leanh::lean_dec(v_a_241_);
                if v_isShared_244_ == 0 {
                    leanh::lean_ctor_set(v___x_243_, 0, v_fst_245_);
                    v___x_247_ = v___x_243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_248_, 0, v_fst_245_);
                    v___x_247_ = v_reuseFailAlloc_248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_247_;
            }
            3 => {
                if v_isShared_253_ == 0 {
                    v___x_255_ = v___x_252_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_256_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
                    v___x_255_ = v_reuseFailAlloc_256_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_255_;
            }
            5 => {
                if v_isShared_261_ == 0 {
                    v___x_263_ = v___x_260_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_264_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
                    v___x_263_ = v_reuseFailAlloc_264_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_263_;
            }
            7 => {
                if v_isShared_269_ == 0 {
                    v___x_271_ = v___x_268_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_272_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
                    v___x_271_ = v_reuseFailAlloc_272_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed(
    mut v___x_274_: *mut leanh::LeanObject,
    mut v___x_275_: *mut leanh::LeanObject,
    mut v___x_276_: *mut leanh::LeanObject,
    mut v_k_277_: *mut leanh::LeanObject,
    mut v___y_278_: *mut leanh::LeanObject,
    mut v___y_279_: *mut leanh::LeanObject,
    mut v___y_280_: *mut leanh::LeanObject,
    mut v___y_281_: *mut leanh::LeanObject,
    mut v___y_282_: *mut leanh::LeanObject,
    mut v___y_283_: *mut leanh::LeanObject,
    mut v___y_284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8570__boxed_285_: u8 = 0;
    let mut v___x_8571__boxed_286_: u8 = 0;
    let mut v_res_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8570__boxed_285_ = (leanh::lean_unbox(v___x_275_) as u8);
    v___x_8571__boxed_286_ = (leanh::lean_unbox(v___x_276_) as u8);
    v_res_287_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(
        v___x_274_,
        v___x_8570__boxed_285_,
        v___x_8571__boxed_286_,
        v_k_277_,
        v___y_278_,
        v___y_279_,
        v___y_280_,
        v___y_281_,
        v___y_282_,
        v___y_283_,
    );
    leanh::lean_dec(v___y_283_);
    leanh::lean_dec_ref(v___y_282_);
    leanh::lean_dec(v___y_281_);
    leanh::lean_dec_ref(v___y_280_);
    leanh::lean_dec(v___y_279_);
    leanh::lean_dec_ref(v___y_278_);
    return v_res_287_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg(
    mut v_k_301_: *mut leanh::LeanObject,
    mut v_a_302_: *mut leanh::LeanObject,
    mut v_a_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_305_: u8 = 0;
    let mut v___x_306_: u8 = 0;
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = 0;
    v___x_306_ = 1;
    v___x_307_ = l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0;
    v___x_308_ = leanh::lean_box((v___x_306_) as usize);
    v___x_309_ = leanh::lean_box((v___x_305_) as usize);
    v___f_310_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        11,
        4,
    );
    leanh::lean_closure_set(v___f_310_, 0, v___x_307_);
    leanh::lean_closure_set(v___f_310_, 1, v___x_308_);
    leanh::lean_closure_set(v___f_310_, 2, v___x_309_);
    leanh::lean_closure_set(v___f_310_, 3, v_k_301_);
    v___x_311_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_310_, v_a_302_, v_a_303_);
    return v___x_311_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___boxed(
    mut v_k_312_: *mut leanh::LeanObject,
    mut v_a_313_: *mut leanh::LeanObject,
    mut v_a_314_: *mut leanh::LeanObject,
    mut v_a_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_312_, v_a_313_, v_a_314_);
    leanh::lean_dec(v_a_314_);
    leanh::lean_dec_ref(v_a_313_);
    return v_res_316_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM(
    mut v_00_u03b1_317_: *mut leanh::LeanObject,
    mut v_k_318_: *mut leanh::LeanObject,
    mut v_a_319_: *mut leanh::LeanObject,
    mut v_a_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_318_, v_a_319_, v_a_320_);
    return v___x_322_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___boxed(
    mut v_00_u03b1_323_: *mut leanh::LeanObject,
    mut v_k_324_: *mut leanh::LeanObject,
    mut v_a_325_: *mut leanh::LeanObject,
    mut v_a_326_: *mut leanh::LeanObject,
    mut v_a_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_328_ =
        l_Lean_Elab_Command_withGrindTacticM(v_00_u03b1_323_, v_k_324_, v_a_325_, v_a_326_);
    leanh::lean_dec(v_a_326_);
    leanh::lean_dec_ref(v_a_325_);
    return v_res_328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
}