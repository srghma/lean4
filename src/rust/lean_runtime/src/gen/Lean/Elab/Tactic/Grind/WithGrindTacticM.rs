// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.WithGrindTacticM
// Imports: Lean.Elab.Tactic.Grind.Basic Lean.Elab.Command
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__0_value
        ) as *mut LeanObject,
        3814902364570594393 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0_value: LeanCtorObject<17> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 13
                + 32) as u16,
            other: 13,
            tag: 0,
        },
        m_objs: [
            (((9 as usize) << 1) | 1) as *mut LeanObject,
            (((5 as usize) << 1) | 1) as *mut LeanObject,
            (((8 as usize) << 1) | 1) as *mut LeanObject,
            (((8 as usize) << 1) | 1) as *mut LeanObject,
            (((1000 as usize) << 1) | 1) as *mut LeanObject,
            (((1000 as usize) << 1) | 1) as *mut LeanObject,
            (((100000 as usize) << 1) | 1) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            (((1000 as usize) << 1) | 1) as *mut LeanObject,
            (((1048576 as usize) << 1) | 1) as *mut LeanObject,
            (((10 as usize) << 1) | 1) as *mut LeanObject,
            (((50 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            72340168526266368 as *mut LeanObject,
            72340172821299200 as *mut LeanObject,
            72340172838076417 as *mut LeanObject,
            72339073326448897 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    v___x_168_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_168_;
}
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    v___x_169_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__2,
    );
    v___x_170_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_170_, 0, v___x_169_);
    return v___x_170_;
}
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    v___x_171_ = lean_box(0);
    v___x_172_ = lean_unsigned_to_nat(16);
    v___x_173_ = lean_mk_array(v___x_172_, v___x_171_);
    return v___x_173_;
}
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
    v___x_174_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__4,
    );
    v___x_175_ = lean_unsigned_to_nat(0);
    v___x_176_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_176_, 0, v___x_175_);
    lean_ctor_set(v___x_176_, 1, v___x_174_);
    return v___x_176_;
}
pub unsafe fn _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    v___x_177_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__5,
    );
    v___x_178_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__3,
    );
    v___x_179_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_179_, 0, v___x_178_);
    lean_ctor_set(v___x_179_, 1, v___x_178_);
    lean_ctor_set(v___x_179_, 2, v___x_177_);
    lean_ctor_set(v___x_179_, 3, v___x_177_);
    return v___x_179_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0(
    mut v___x_180_: u8,
    mut v_a_181_: *mut LeanObject,
    mut v___x_182_: u8,
    mut v___y_183_: *mut LeanObject,
    mut v___y_184_: *mut LeanObject,
    mut v___y_185_: *mut LeanObject,
    mut v___y_186_: *mut LeanObject,
    mut v___y_187_: *mut LeanObject,
    mut v___y_188_: *mut LeanObject,
    mut v___y_189_: *mut LeanObject,
    mut v___y_190_: *mut LeanObject,
    mut v___y_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    v___x_193_ = lean_st_ref_get(v___y_185_);
    v___x_194_ = lean_st_ref_get(v___y_187_);
    v___x_195_ = l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__1;
    v___x_196_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_196_, 0, v___x_195_);
    lean_ctor_set_uint8(
        v___x_196_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_180_,
    );
    lean_inc(v___y_183_);
    lean_inc_ref(v___y_186_);
    lean_inc_ref(v___y_184_);
    v___x_197_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_197_, 0, v___x_196_);
    lean_ctor_set(v___x_197_, 1, v___y_184_);
    lean_ctor_set(v___x_197_, 2, v___y_186_);
    lean_ctor_set(v___x_197_, 3, v___y_183_);
    lean_ctor_set(v___x_197_, 4, v_a_181_);
    lean_ctor_set_uint8(
        v___x_197_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_182_,
    );
    v___x_198_ = lean_box(0);
    v___x_199_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6_once
        ),
        _init_l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___closed__6,
    );
    v___x_200_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_200_, 0, v___x_194_);
    lean_ctor_set(v___x_200_, 1, v___x_193_);
    lean_ctor_set(v___x_200_, 2, v___x_198_);
    lean_ctor_set(v___x_200_, 3, v___x_199_);
    v___x_201_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_201_, 0, v___x_197_);
    lean_ctor_set(v___x_201_, 1, v___x_200_);
    v___x_202_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_202_, 0, v___x_201_);
    return v___x_202_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed(
    mut v___x_203_: *mut LeanObject,
    mut v_a_204_: *mut LeanObject,
    mut v___x_205_: *mut LeanObject,
    mut v___y_206_: *mut LeanObject,
    mut v___y_207_: *mut LeanObject,
    mut v___y_208_: *mut LeanObject,
    mut v___y_209_: *mut LeanObject,
    mut v___y_210_: *mut LeanObject,
    mut v___y_211_: *mut LeanObject,
    mut v___y_212_: *mut LeanObject,
    mut v___y_213_: *mut LeanObject,
    mut v___y_214_: *mut LeanObject,
    mut v___y_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8495__boxed_216_: u8 = 0;
    let mut v___x_8497__boxed_217_: u8 = 0;
    let mut v_res_218_: *mut LeanObject = core::ptr::null_mut();
    v___x_8495__boxed_216_ = (lean_unbox(v___x_203_) as u8);
    v___x_8497__boxed_217_ = (lean_unbox(v___x_205_) as u8);
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
    lean_dec(v___y_214_);
    lean_dec_ref(v___y_213_);
    lean_dec(v___y_212_);
    lean_dec_ref(v___y_211_);
    lean_dec(v___y_210_);
    lean_dec_ref(v___y_209_);
    lean_dec(v___y_208_);
    lean_dec_ref(v___y_207_);
    lean_dec(v___y_206_);
    return v_res_218_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1(
    mut v___x_219_: *mut LeanObject,
    mut v___x_220_: u8,
    mut v___x_221_: u8,
    mut v_k_222_: *mut LeanObject,
    mut v___y_223_: *mut LeanObject,
    mut v___y_224_: *mut LeanObject,
    mut v___y_225_: *mut LeanObject,
    mut v___y_226_: *mut LeanObject,
    mut v___y_227_: *mut LeanObject,
    mut v___y_228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v_fst_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_249_: u8 = 0;
    let mut v_a_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_253_: u8 = 0;
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_257_: u8 = 0;
    let mut v_a_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_261_: u8 = 0;
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_265_: u8 = 0;
    let mut v_a_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_269_: u8 = 0;
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_230_ = l_Lean_Meta_Grind_mkDefaultParams(
                    v___x_219_, v___y_225_, v___y_226_, v___y_227_, v___y_228_,
                );
                if lean_obj_tag(v___x_230_) == 0 {
                    v_a_231_ = lean_ctor_get(v___x_230_, 0);
                    lean_inc_n(v_a_231_, 2);
                    lean_dec_ref_known(v___x_230_, 1);
                    v___x_232_ = lean_box((v___x_220_) as usize);
                    v___x_233_ = lean_box((v___x_221_) as usize);
                    v___f_234_ = lean_alloc_closure(
                        l_Lean_Elab_Command_withGrindTacticM___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        13,
                        3,
                    );
                    lean_closure_set(v___f_234_, 0, v___x_232_);
                    lean_closure_set(v___f_234_, 1, v_a_231_);
                    lean_closure_set(v___f_234_, 2, v___x_233_);
                    v___x_235_ = lean_box(0);
                    v___x_236_ = l_Lean_Meta_Grind_GrindM_run___redArg(
                        v___f_234_, v_a_231_, v___x_235_, v___y_225_, v___y_226_, v___y_227_,
                        v___y_228_,
                    );
                    if lean_obj_tag(v___x_236_) == 0 {
                        v_a_237_ = lean_ctor_get(v___x_236_, 0);
                        lean_inc(v_a_237_);
                        lean_dec_ref_known(v___x_236_, 1);
                        v_fst_238_ = lean_ctor_get(v_a_237_, 0);
                        lean_inc(v_fst_238_);
                        v_snd_239_ = lean_ctor_get(v_a_237_, 1);
                        lean_inc(v_snd_239_);
                        lean_dec(v_a_237_);
                        v___x_240_ = l_Lean_Elab_Tactic_Grind_GrindTacticM_run___redArg(
                            v_k_222_, v_fst_238_, v_snd_239_, v___y_223_, v___y_224_, v___y_225_,
                            v___y_226_, v___y_227_, v___y_228_,
                        );
                        if lean_obj_tag(v___x_240_) == 0 {
                            v_a_241_ = lean_ctor_get(v___x_240_, 0);
                            v_isSharedCheck_249_ = (!lean_is_exclusive(v___x_240_)) as u8;
                            if v_isSharedCheck_249_ == 0 {
                                v___x_243_ = v___x_240_;
                                v_isShared_244_ = v_isSharedCheck_249_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_241_);
                                lean_dec(v___x_240_);
                                v___x_243_ = lean_box(0);
                                v_isShared_244_ = v_isSharedCheck_249_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_250_ = lean_ctor_get(v___x_240_, 0);
                            v_isSharedCheck_257_ = (!lean_is_exclusive(v___x_240_)) as u8;
                            if v_isSharedCheck_257_ == 0 {
                                v___x_252_ = v___x_240_;
                                v_isShared_253_ = v_isSharedCheck_257_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_250_);
                                lean_dec(v___x_240_);
                                v___x_252_ = lean_box(0);
                                v_isShared_253_ = v_isSharedCheck_257_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_k_222_);
                        v_a_258_ = lean_ctor_get(v___x_236_, 0);
                        v_isSharedCheck_265_ = (!lean_is_exclusive(v___x_236_)) as u8;
                        if v_isSharedCheck_265_ == 0 {
                            v___x_260_ = v___x_236_;
                            v_isShared_261_ = v_isSharedCheck_265_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_258_);
                            lean_dec(v___x_236_);
                            v___x_260_ = lean_box(0);
                            v_isShared_261_ = v_isSharedCheck_265_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_k_222_);
                    v_a_266_ = lean_ctor_get(v___x_230_, 0);
                    v_isSharedCheck_273_ = (!lean_is_exclusive(v___x_230_)) as u8;
                    if v_isSharedCheck_273_ == 0 {
                        v___x_268_ = v___x_230_;
                        v_isShared_269_ = v_isSharedCheck_273_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_266_);
                        lean_dec(v___x_230_);
                        v___x_268_ = lean_box(0);
                        v_isShared_269_ = v_isSharedCheck_273_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_245_ = lean_ctor_get(v_a_241_, 0);
                lean_inc(v_fst_245_);
                lean_dec(v_a_241_);
                if v_isShared_244_ == 0 {
                    lean_ctor_set(v___x_243_, 0, v_fst_245_);
                    v___x_247_ = v___x_243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_248_, 0, v_fst_245_);
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
                    v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
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
                    v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
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
                    v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
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
    mut v___x_274_: *mut LeanObject,
    mut v___x_275_: *mut LeanObject,
    mut v___x_276_: *mut LeanObject,
    mut v_k_277_: *mut LeanObject,
    mut v___y_278_: *mut LeanObject,
    mut v___y_279_: *mut LeanObject,
    mut v___y_280_: *mut LeanObject,
    mut v___y_281_: *mut LeanObject,
    mut v___y_282_: *mut LeanObject,
    mut v___y_283_: *mut LeanObject,
    mut v___y_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8570__boxed_285_: u8 = 0;
    let mut v___x_8571__boxed_286_: u8 = 0;
    let mut v_res_287_: *mut LeanObject = core::ptr::null_mut();
    v___x_8570__boxed_285_ = (lean_unbox(v___x_275_) as u8);
    v___x_8571__boxed_286_ = (lean_unbox(v___x_276_) as u8);
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
    lean_dec(v___y_283_);
    lean_dec_ref(v___y_282_);
    lean_dec(v___y_281_);
    lean_dec_ref(v___y_280_);
    lean_dec(v___y_279_);
    lean_dec_ref(v___y_278_);
    return v_res_287_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg(
    mut v_k_301_: *mut LeanObject,
    mut v_a_302_: *mut LeanObject,
    mut v_a_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_305_: u8 = 0;
    let mut v___x_306_: u8 = 0;
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    v___x_305_ = 0;
    v___x_306_ = 1;
    v___x_307_ = l_Lean_Elab_Command_withGrindTacticM___redArg___closed__0;
    v___x_308_ = lean_box((v___x_306_) as usize);
    v___x_309_ = lean_box((v___x_305_) as usize);
    v___f_310_ = lean_alloc_closure(
        l_Lean_Elab_Command_withGrindTacticM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        11,
        4,
    );
    lean_closure_set(v___f_310_, 0, v___x_307_);
    lean_closure_set(v___f_310_, 1, v___x_308_);
    lean_closure_set(v___f_310_, 2, v___x_309_);
    lean_closure_set(v___f_310_, 3, v_k_301_);
    v___x_311_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_310_, v_a_302_, v_a_303_);
    return v___x_311_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___redArg___boxed(
    mut v_k_312_: *mut LeanObject,
    mut v_a_313_: *mut LeanObject,
    mut v_a_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_316_: *mut LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_312_, v_a_313_, v_a_314_);
    lean_dec(v_a_314_);
    lean_dec_ref(v_a_313_);
    return v_res_316_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM(
    mut v_00_u03b1_317_: *mut LeanObject,
    mut v_k_318_: *mut LeanObject,
    mut v_a_319_: *mut LeanObject,
    mut v_a_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = l_Lean_Elab_Command_withGrindTacticM___redArg(v_k_318_, v_a_319_, v_a_320_);
    return v___x_322_;
}
pub unsafe fn l_Lean_Elab_Command_withGrindTacticM___boxed(
    mut v_00_u03b1_323_: *mut LeanObject,
    mut v_k_324_: *mut LeanObject,
    mut v_a_325_: *mut LeanObject,
    mut v_a_326_: *mut LeanObject,
    mut v_a_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_328_: *mut LeanObject = core::ptr::null_mut();
    v_res_328_ =
        l_Lean_Elab_Command_withGrindTacticM(v_00_u03b1_323_, v_k_324_, v_a_325_, v_a_326_);
    lean_dec(v_a_326_);
    lean_dec_ref(v_a_325_);
    return v_res_328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
}
