// Lean compiler output
// Module: Lean.Elab.DeclarationRange
// Imports: Lean.Parser.Command
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getKind,
    l_Lean_Syntax_isIdent, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_DeclarationRange_ofStringPositions;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addDeclarationRanges___redArg;
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_getRange_x3f;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__3_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0],
    };
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__3_value)
                as *mut LeanObject,
            11064845058293668901 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [101, 120, 97, 109, 112, 108, 101, 0],
};
static mut l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__2_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value)
            as *mut LeanObject,
        16587644253004373100 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value)
            as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(
    mut v_val_183_: *mut LeanObject,
    mut v_toPure_184_: *mut LeanObject,
    mut v_fileMap_185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    v_start_186_ = lean_ctor_get(v_val_183_, 0);
    v_stop_187_ = lean_ctor_get(v_val_183_, 1);
    v___x_188_ =
        l_Lean_DeclarationRange_ofStringPositions(v_fileMap_185_, v_start_186_, v_stop_187_);
    v___x_189_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_189_, 0, v___x_188_);
    v___x_190_ = lean_apply_2(v_toPure_184_, lean_box(0), v___x_189_);
    return v___x_190_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed(
    mut v_val_191_: *mut LeanObject,
    mut v_toPure_192_: *mut LeanObject,
    mut v_fileMap_193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_194_: *mut LeanObject = core::ptr::null_mut();
    v_res_194_ = l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(
        v_val_191_,
        v_toPure_192_,
        v_fileMap_193_,
    );
    lean_dec_ref(v_val_191_);
    return v_res_194_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___redArg(
    mut v_inst_195_: *mut LeanObject,
    mut v_inst_196_: *mut LeanObject,
    mut v_stx_197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: u8 = 0;
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_198_ = lean_ctor_get(v_inst_195_, 0);
    lean_inc_ref(v_toApplicative_198_);
    v_toBind_199_ = lean_ctor_get(v_inst_195_, 1);
    lean_inc(v_toBind_199_);
    lean_dec_ref(v_inst_195_);
    v_toPure_200_ = lean_ctor_get(v_toApplicative_198_, 1);
    lean_inc(v_toPure_200_);
    lean_dec_ref(v_toApplicative_198_);
    v___x_201_ = 0;
    v___x_202_ = l_Lean_Syntax_getRange_x3f(v_stx_197_, v___x_201_);
    if lean_obj_tag(v___x_202_) == 1 {
        let mut v_val_203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
        v_val_203_ = lean_ctor_get(v___x_202_, 0);
        lean_inc(v_val_203_);
        lean_dec_ref_known(v___x_202_, 1);
        v___f_204_ = lean_alloc_closure(
            l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_204_, 0, v_val_203_);
        lean_closure_set(v___f_204_, 1, v_toPure_200_);
        v___x_205_ = lean_apply_4(
            v_toBind_199_,
            lean_box(0),
            lean_box(0),
            v_inst_196_,
            v___f_204_,
        );
        return v___x_205_;
    } else {
        let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_202_);
        lean_dec(v_toBind_199_);
        lean_dec(v_inst_196_);
        v___x_206_ = lean_box(0);
        v___x_207_ = lean_apply_2(v_toPure_200_, lean_box(0), v___x_206_);
        return v___x_207_;
    }
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___redArg___boxed(
    mut v_inst_208_: *mut LeanObject,
    mut v_inst_209_: *mut LeanObject,
    mut v_stx_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_211_: *mut LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_208_, v_inst_209_, v_stx_210_);
    lean_dec(v_stx_210_);
    return v_res_211_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f(
    mut v_m_212_: *mut LeanObject,
    mut v_inst_213_: *mut LeanObject,
    mut v_inst_214_: *mut LeanObject,
    mut v_stx_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    v___x_216_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_213_, v_inst_214_, v_stx_215_);
    return v___x_216_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___boxed(
    mut v_m_217_: *mut LeanObject,
    mut v_inst_218_: *mut LeanObject,
    mut v_inst_219_: *mut LeanObject,
    mut v_stx_220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_221_: *mut LeanObject = core::ptr::null_mut();
    v_res_221_ =
        l_Lean_Elab_getDeclarationRange_x3f(v_m_217_, v_inst_218_, v_inst_219_, v_stx_220_);
    lean_dec(v_stx_220_);
    return v_res_221_;
}
pub unsafe fn l_Lean_Elab_getDeclarationSelectionRef(
    mut v_stx_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: u8 = 0;
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: u8 = 0;
    let mut v___x_242_: u8 = 0;
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_246_: u8 = 0;
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_235_ = l_Lean_Elab_getDeclarationSelectionRef___closed__4;
                lean_inc(v_stx_231_);
                v___x_236_ = l_Lean_Syntax_isOfKind(v_stx_231_, v___x_235_);
                if v___x_236_ == 0 {
                    v___x_237_ = lean_unsigned_to_nat(1);
                    v___x_238_ = l_Lean_Syntax_getArg(v_stx_231_, v___x_237_);
                    v___x_239_ = lean_unsigned_to_nat(0);
                    v___x_240_ = l_Lean_Syntax_getArg(v___x_238_, v___x_239_);
                    v___x_241_ = l_Lean_Syntax_isIdent(v___x_240_);
                    if v___x_241_ == 0 {
                        lean_dec(v___x_240_);
                        v___x_242_ = l_Lean_Syntax_isIdent(v___x_238_);
                        if v___x_242_ == 0 {
                            lean_dec(v___x_238_);
                            v___x_243_ = l_Lean_Syntax_getArg(v_stx_231_, v___x_239_);
                            lean_dec(v_stx_231_);
                            return v___x_243_;
                        } else {
                            lean_dec(v_stx_231_);
                            return v___x_238_;
                        }
                    } else {
                        lean_dec(v___x_238_);
                        lean_dec(v_stx_231_);
                        return v___x_240_;
                    }
                } else {
                    v___x_244_ = lean_unsigned_to_nat(3);
                    v___x_245_ = l_Lean_Syntax_getArg(v_stx_231_, v___x_244_);
                    v___x_246_ = l_Lean_Syntax_isNone(v___x_245_);
                    if v___x_246_ == 0 {
                        if v___x_236_ == 0 {
                            lean_dec(v___x_245_);
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_stx_231_);
                            v___x_247_ = lean_unsigned_to_nat(0);
                            v___x_248_ = l_Lean_Syntax_getArg(v___x_245_, v___x_247_);
                            lean_dec(v___x_245_);
                            return v___x_248_;
                        }
                    } else {
                        lean_dec(v___x_245_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_233_ = lean_unsigned_to_nat(1);
                v___x_234_ = l_Lean_Syntax_getArg(v_stx_231_, v___x_233_);
                lean_dec(v_stx_231_);
                return v___x_234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(
    mut v_val_249_: *mut LeanObject,
    mut v_x_250_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_250_) == 0 {
        lean_inc_ref(v_val_249_);
        return v_val_249_;
    } else {
        let mut v_val_251_: *mut LeanObject = core::ptr::null_mut();
        v_val_251_ = lean_ctor_get(v_x_250_, 0);
        lean_inc(v_val_251_);
        return v_val_251_;
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed(
    mut v_val_252_: *mut LeanObject,
    mut v_x_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_254_: *mut LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(v_val_252_, v_x_253_);
    lean_dec(v_x_253_);
    lean_dec_ref(v_val_252_);
    return v_res_254_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1(
    mut v_val_255_: *mut LeanObject,
    mut v_inst_256_: *mut LeanObject,
    mut v_inst_257_: *mut LeanObject,
    mut v_declName_258_: *mut LeanObject,
    mut v_selectionRange_259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    v___x_260_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_260_, 0, v_val_255_);
    lean_ctor_set(v___x_260_, 1, v_selectionRange_259_);
    v___x_261_ =
        l_Lean_addDeclarationRanges___redArg(v_inst_256_, v_inst_257_, v_declName_258_, v___x_260_);
    return v___x_261_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(
    mut v_toFunctor_262_: *mut LeanObject,
    mut v_inst_263_: *mut LeanObject,
    mut v_inst_264_: *mut LeanObject,
    mut v_declName_265_: *mut LeanObject,
    mut v_inst_266_: *mut LeanObject,
    mut v_selectionRangeStx_267_: *mut LeanObject,
    mut v_toBind_268_: *mut LeanObject,
    mut v_toPure_269_: *mut LeanObject,
    mut v_____x_270_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_270_) == 1 {
        let mut v_val_271_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_269_);
        v_val_271_ = lean_ctor_get(v_____x_270_, 0);
        lean_inc_n(v_val_271_, 2);
        lean_dec_ref_known(v_____x_270_, 1);
        v_map_272_ = lean_ctor_get(v_toFunctor_262_, 0);
        lean_inc(v_map_272_);
        lean_dec_ref(v_toFunctor_262_);
        v___f_273_ = lean_alloc_closure(
            l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_273_, 0, v_val_271_);
        lean_inc_ref(v_inst_263_);
        v___f_274_ = lean_alloc_closure(
            l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_274_, 0, v_val_271_);
        lean_closure_set(v___f_274_, 1, v_inst_263_);
        lean_closure_set(v___f_274_, 2, v_inst_264_);
        lean_closure_set(v___f_274_, 3, v_declName_265_);
        v___x_275_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(
            v_inst_263_,
            v_inst_266_,
            v_selectionRangeStx_267_,
        );
        v___x_276_ = lean_apply_4(v_map_272_, lean_box(0), lean_box(0), v___f_273_, v___x_275_);
        v___x_277_ = lean_apply_4(
            v_toBind_268_,
            lean_box(0),
            lean_box(0),
            v___x_276_,
            v___f_274_,
        );
        return v___x_277_;
    } else {
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____x_270_);
        lean_dec(v_toBind_268_);
        lean_dec(v_inst_266_);
        lean_dec(v_declName_265_);
        lean_dec_ref(v_inst_264_);
        lean_dec_ref(v_inst_263_);
        lean_dec_ref(v_toFunctor_262_);
        v___x_278_ = lean_box(0);
        v___x_279_ = lean_apply_2(v_toPure_269_, lean_box(0), v___x_278_);
        return v___x_279_;
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed(
    mut v_toFunctor_280_: *mut LeanObject,
    mut v_inst_281_: *mut LeanObject,
    mut v_inst_282_: *mut LeanObject,
    mut v_declName_283_: *mut LeanObject,
    mut v_inst_284_: *mut LeanObject,
    mut v_selectionRangeStx_285_: *mut LeanObject,
    mut v_toBind_286_: *mut LeanObject,
    mut v_toPure_287_: *mut LeanObject,
    mut v_____x_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_289_: *mut LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(
        v_toFunctor_280_,
        v_inst_281_,
        v_inst_282_,
        v_declName_283_,
        v_inst_284_,
        v_selectionRangeStx_285_,
        v_toBind_286_,
        v_toPure_287_,
        v_____x_288_,
    );
    lean_dec(v_selectionRangeStx_285_);
    return v_res_289_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(
    mut v_inst_290_: *mut LeanObject,
    mut v_inst_291_: *mut LeanObject,
    mut v_inst_292_: *mut LeanObject,
    mut v_declName_293_: *mut LeanObject,
    mut v_rangeStx_294_: *mut LeanObject,
    mut v_selectionRangeStx_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_296_ = lean_ctor_get(v_inst_290_, 0);
    v_toBind_297_ = lean_ctor_get(v_inst_290_, 1);
    lean_inc_n(v_toBind_297_, 2);
    v_toFunctor_298_ = lean_ctor_get(v_toApplicative_296_, 0);
    lean_inc_ref(v_toFunctor_298_);
    v_toPure_299_ = lean_ctor_get(v_toApplicative_296_, 1);
    lean_inc(v_toPure_299_);
    lean_inc(v_inst_292_);
    lean_inc_ref(v_inst_290_);
    v___x_300_ =
        l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_290_, v_inst_292_, v_rangeStx_294_);
    v___f_301_ = lean_alloc_closure(
        l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_301_, 0, v_toFunctor_298_);
    lean_closure_set(v___f_301_, 1, v_inst_290_);
    lean_closure_set(v___f_301_, 2, v_inst_291_);
    lean_closure_set(v___f_301_, 3, v_declName_293_);
    lean_closure_set(v___f_301_, 4, v_inst_292_);
    lean_closure_set(v___f_301_, 5, v_selectionRangeStx_295_);
    lean_closure_set(v___f_301_, 6, v_toBind_297_);
    lean_closure_set(v___f_301_, 7, v_toPure_299_);
    v___x_302_ = lean_apply_4(
        v_toBind_297_,
        lean_box(0),
        lean_box(0),
        v___x_300_,
        v___f_301_,
    );
    return v___x_302_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___boxed(
    mut v_inst_303_: *mut LeanObject,
    mut v_inst_304_: *mut LeanObject,
    mut v_inst_305_: *mut LeanObject,
    mut v_declName_306_: *mut LeanObject,
    mut v_rangeStx_307_: *mut LeanObject,
    mut v_selectionRangeStx_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_309_: *mut LeanObject = core::ptr::null_mut();
    v_res_309_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(
        v_inst_303_,
        v_inst_304_,
        v_inst_305_,
        v_declName_306_,
        v_rangeStx_307_,
        v_selectionRangeStx_308_,
    );
    lean_dec(v_rangeStx_307_);
    return v_res_309_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax(
    mut v_m_310_: *mut LeanObject,
    mut v_inst_311_: *mut LeanObject,
    mut v_inst_312_: *mut LeanObject,
    mut v_inst_313_: *mut LeanObject,
    mut v_declName_314_: *mut LeanObject,
    mut v_rangeStx_315_: *mut LeanObject,
    mut v_selectionRangeStx_316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    v___x_317_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(
        v_inst_311_,
        v_inst_312_,
        v_inst_313_,
        v_declName_314_,
        v_rangeStx_315_,
        v_selectionRangeStx_316_,
    );
    return v___x_317_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___boxed(
    mut v_m_318_: *mut LeanObject,
    mut v_inst_319_: *mut LeanObject,
    mut v_inst_320_: *mut LeanObject,
    mut v_inst_321_: *mut LeanObject,
    mut v_declName_322_: *mut LeanObject,
    mut v_rangeStx_323_: *mut LeanObject,
    mut v_selectionRangeStx_324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_325_: *mut LeanObject = core::ptr::null_mut();
    v_res_325_ = l_Lean_Elab_addDeclarationRangesFromSyntax(
        v_m_318_,
        v_inst_319_,
        v_inst_320_,
        v_inst_321_,
        v_declName_322_,
        v_rangeStx_323_,
        v_selectionRangeStx_324_,
    );
    lean_dec(v_rangeStx_323_);
    return v_res_325_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(
    mut v_inst_335_: *mut LeanObject,
    mut v_inst_336_: *mut LeanObject,
    mut v_inst_337_: *mut LeanObject,
    mut v_declName_338_: *mut LeanObject,
    mut v_modsStx_339_: *mut LeanObject,
    mut v_declStx_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: u8 = 0;
    lean_inc(v_declStx_340_);
    v___x_341_ = l_Lean_Syntax_getKind(v_declStx_340_);
    v___x_342_ = l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1;
    v___x_343_ = lean_name_eq(v___x_341_, v___x_342_);
    lean_dec(v___x_341_);
    if v___x_343_ == 0 {
        let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
        let mut v_stx_350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
        v___x_344_ = lean_unsigned_to_nat(2);
        v___x_345_ = lean_mk_empty_array_with_capacity(v___x_344_);
        v___x_346_ = lean_array_push(v___x_345_, v_modsStx_339_);
        lean_inc(v_declStx_340_);
        v___x_347_ = lean_array_push(v___x_346_, v_declStx_340_);
        v___x_348_ = l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3;
        v___x_349_ = lean_box(2);
        v_stx_350_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v_stx_350_, 0, v___x_349_);
        lean_ctor_set(v_stx_350_, 1, v___x_348_);
        lean_ctor_set(v_stx_350_, 2, v___x_347_);
        v___x_351_ = l_Lean_Elab_getDeclarationSelectionRef(v_declStx_340_);
        v___x_352_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(
            v_inst_335_,
            v_inst_336_,
            v_inst_337_,
            v_declName_338_,
            v_stx_350_,
            v___x_351_,
        );
        lean_dec_ref_known(v_stx_350_, 3);
        return v___x_352_;
    } else {
        let mut v_toApplicative_353_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_354_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_declStx_340_);
        lean_dec(v_modsStx_339_);
        lean_dec(v_declName_338_);
        lean_dec(v_inst_337_);
        lean_dec_ref(v_inst_336_);
        v_toApplicative_353_ = lean_ctor_get(v_inst_335_, 0);
        lean_inc_ref(v_toApplicative_353_);
        lean_dec_ref(v_inst_335_);
        v_toPure_354_ = lean_ctor_get(v_toApplicative_353_, 1);
        lean_inc(v_toPure_354_);
        lean_dec_ref(v_toApplicative_353_);
        v___x_355_ = lean_box(0);
        v___x_356_ = lean_apply_2(v_toPure_354_, lean_box(0), v___x_355_);
        return v___x_356_;
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesForBuiltin(
    mut v_m_357_: *mut LeanObject,
    mut v_inst_358_: *mut LeanObject,
    mut v_inst_359_: *mut LeanObject,
    mut v_inst_360_: *mut LeanObject,
    mut v_declName_361_: *mut LeanObject,
    mut v_modsStx_362_: *mut LeanObject,
    mut v_declStx_363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(
        v_inst_358_,
        v_inst_359_,
        v_inst_360_,
        v_declName_361_,
        v_modsStx_362_,
        v_declStx_363_,
    );
    return v___x_364_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeclarationRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_DeclarationRange(builtin);
}
