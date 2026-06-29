// Lean compiler output
// Module: Lean.Elab.DeclarationRange
// Imports: Lean.Parser.Command
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_Syntax_isIdent, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_DeclarationRange_ofStringPositions;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addDeclarationRanges___redArg;
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_getRange_x3f;
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__3_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_getDeclarationSelectionRef___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__3_value)
            as *mut crate::leanh::LeanObject,
        11064845058293668901 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_getDeclarationSelectionRef___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_getDeclarationSelectionRef___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16587644253004373100 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(
    mut v_val_183_: *mut crate::leanh::LeanObject,
    mut v_toPure_184_: *mut crate::leanh::LeanObject,
    mut v_fileMap_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_186_ = crate::leanh::lean_ctor_get(v_val_183_, 0);
    v_stop_187_ = crate::leanh::lean_ctor_get(v_val_183_, 1);
    v___x_188_ =
        l_Lean_DeclarationRange_ofStringPositions(v_fileMap_185_, v_start_186_, v_stop_187_);
    v___x_189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_189_, 0, v___x_188_);
    v___x_190_ = crate::leanh::lean_apply_2(v_toPure_184_, crate::leanh::lean_box(0), v___x_189_);
    return v___x_190_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed(
    mut v_val_191_: *mut crate::leanh::LeanObject,
    mut v_toPure_192_: *mut crate::leanh::LeanObject,
    mut v_fileMap_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_194_ = l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(
        v_val_191_,
        v_toPure_192_,
        v_fileMap_193_,
    );
    crate::leanh::lean_dec_ref(v_val_191_);
    return v_res_194_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___redArg(
    mut v_inst_195_: *mut crate::leanh::LeanObject,
    mut v_inst_196_: *mut crate::leanh::LeanObject,
    mut v_stx_197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: u8 = 0;
    let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_198_ = crate::leanh::lean_ctor_get(v_inst_195_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_198_);
    v_toBind_199_ = crate::leanh::lean_ctor_get(v_inst_195_, 1);
    crate::leanh::lean_inc(v_toBind_199_);
    crate::leanh::lean_dec_ref(v_inst_195_);
    v_toPure_200_ = crate::leanh::lean_ctor_get(v_toApplicative_198_, 1);
    crate::leanh::lean_inc(v_toPure_200_);
    crate::leanh::lean_dec_ref(v_toApplicative_198_);
    v___x_201_ = 0;
    v___x_202_ = l_Lean_Syntax_getRange_x3f(v_stx_197_, v___x_201_);
    if crate::leanh::lean_obj_tag(v___x_202_) == 1 {
        let mut v_val_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_203_ = crate::leanh::lean_ctor_get(v___x_202_, 0);
        crate::leanh::lean_inc(v_val_203_);
        crate::leanh::lean_dec_ref_known(v___x_202_, 1);
        v___f_204_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_204_, 0, v_val_203_);
        crate::leanh::lean_closure_set(v___f_204_, 1, v_toPure_200_);
        v___x_205_ = crate::leanh::lean_apply_4(
            v_toBind_199_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_196_,
            v___f_204_,
        );
        return v___x_205_;
    } else {
        let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_202_);
        crate::leanh::lean_dec(v_toBind_199_);
        crate::leanh::lean_dec(v_inst_196_);
        v___x_206_ = crate::leanh::lean_box(0);
        v___x_207_ =
            crate::leanh::lean_apply_2(v_toPure_200_, crate::leanh::lean_box(0), v___x_206_);
        return v___x_207_;
    }
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___redArg___boxed(
    mut v_inst_208_: *mut crate::leanh::LeanObject,
    mut v_inst_209_: *mut crate::leanh::LeanObject,
    mut v_stx_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_208_, v_inst_209_, v_stx_210_);
    crate::leanh::lean_dec(v_stx_210_);
    return v_res_211_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f(
    mut v_m_212_: *mut crate::leanh::LeanObject,
    mut v_inst_213_: *mut crate::leanh::LeanObject,
    mut v_inst_214_: *mut crate::leanh::LeanObject,
    mut v_stx_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_216_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_213_, v_inst_214_, v_stx_215_);
    return v___x_216_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___boxed(
    mut v_m_217_: *mut crate::leanh::LeanObject,
    mut v_inst_218_: *mut crate::leanh::LeanObject,
    mut v_inst_219_: *mut crate::leanh::LeanObject,
    mut v_stx_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_221_ =
        l_Lean_Elab_getDeclarationRange_x3f(v_m_217_, v_inst_218_, v_inst_219_, v_stx_220_);
    crate::leanh::lean_dec(v_stx_220_);
    return v_res_221_;
}
pub unsafe fn l_Lean_Elab_getDeclarationSelectionRef(
    mut v_stx_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: u8 = 0;
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: u8 = 0;
    let mut v___x_242_: u8 = 0;
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: u8 = 0;
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_235_ = l_Lean_Elab_getDeclarationSelectionRef___closed__4;
                crate::leanh::lean_inc(v_stx_231_);
                v___x_236_ = l_Lean_Syntax_isOfKind(v_stx_231_, v___x_235_);
                if v___x_236_ == 0 {
                    v___x_237_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_238_ = l_Lean_Syntax_getArg(v_stx_231_, v___x_237_);
                    v___x_239_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_240_ = l_Lean_Syntax_getArg(v___x_238_, v___x_239_);
                    v___x_241_ = l_Lean_Syntax_isIdent(v___x_240_);
                    if v___x_241_ == 0 {
                        crate::leanh::lean_dec(v___x_240_);
                        v___x_242_ = l_Lean_Syntax_isIdent(v___x_238_);
                        if v___x_242_ == 0 {
                            crate::leanh::lean_dec(v___x_238_);
                            v___x_243_ = l_Lean_Syntax_getArg(v_stx_231_, v___x_239_);
                            crate::leanh::lean_dec(v_stx_231_);
                            return v___x_243_;
                        } else {
                            crate::leanh::lean_dec(v_stx_231_);
                            return v___x_238_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_238_);
                        crate::leanh::lean_dec(v_stx_231_);
                        return v___x_240_;
                    }
                } else {
                    v___x_244_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_245_ = l_Lean_Syntax_getArg(v_stx_231_, v___x_244_);
                    v___x_246_ = l_Lean_Syntax_isNone(v___x_245_);
                    if v___x_246_ == 0 {
                        if v___x_236_ == 0 {
                            crate::leanh::lean_dec(v___x_245_);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_stx_231_);
                            v___x_247_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_248_ = l_Lean_Syntax_getArg(v___x_245_, v___x_247_);
                            crate::leanh::lean_dec(v___x_245_);
                            return v___x_248_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_245_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_233_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_234_ = l_Lean_Syntax_getArg(v_stx_231_, v___x_233_);
                crate::leanh::lean_dec(v_stx_231_);
                return v___x_234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(
    mut v_val_249_: *mut crate::leanh::LeanObject,
    mut v_x_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_250_) == 0 {
        crate::leanh::lean_inc_ref(v_val_249_);
        return v_val_249_;
    } else {
        let mut v_val_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_251_ = crate::leanh::lean_ctor_get(v_x_250_, 0);
        crate::leanh::lean_inc(v_val_251_);
        return v_val_251_;
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed(
    mut v_val_252_: *mut crate::leanh::LeanObject,
    mut v_x_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(v_val_252_, v_x_253_);
    crate::leanh::lean_dec(v_x_253_);
    crate::leanh::lean_dec_ref(v_val_252_);
    return v_res_254_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1(
    mut v_val_255_: *mut crate::leanh::LeanObject,
    mut v_inst_256_: *mut crate::leanh::LeanObject,
    mut v_inst_257_: *mut crate::leanh::LeanObject,
    mut v_declName_258_: *mut crate::leanh::LeanObject,
    mut v_selectionRange_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_260_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_260_, 0, v_val_255_);
    crate::leanh::lean_ctor_set(v___x_260_, 1, v_selectionRange_259_);
    v___x_261_ =
        l_Lean_addDeclarationRanges___redArg(v_inst_256_, v_inst_257_, v_declName_258_, v___x_260_);
    return v___x_261_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(
    mut v_toFunctor_262_: *mut crate::leanh::LeanObject,
    mut v_inst_263_: *mut crate::leanh::LeanObject,
    mut v_inst_264_: *mut crate::leanh::LeanObject,
    mut v_declName_265_: *mut crate::leanh::LeanObject,
    mut v_inst_266_: *mut crate::leanh::LeanObject,
    mut v_selectionRangeStx_267_: *mut crate::leanh::LeanObject,
    mut v_toBind_268_: *mut crate::leanh::LeanObject,
    mut v_toPure_269_: *mut crate::leanh::LeanObject,
    mut v_____x_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_270_) == 1 {
        let mut v_val_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_269_);
        v_val_271_ = crate::leanh::lean_ctor_get(v_____x_270_, 0);
        crate::leanh::lean_inc_n(v_val_271_, 2);
        crate::leanh::lean_dec_ref_known(v_____x_270_, 1);
        v_map_272_ = crate::leanh::lean_ctor_get(v_toFunctor_262_, 0);
        crate::leanh::lean_inc(v_map_272_);
        crate::leanh::lean_dec_ref(v_toFunctor_262_);
        v___f_273_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_273_, 0, v_val_271_);
        crate::leanh::lean_inc_ref(v_inst_263_);
        v___f_274_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_274_, 0, v_val_271_);
        crate::leanh::lean_closure_set(v___f_274_, 1, v_inst_263_);
        crate::leanh::lean_closure_set(v___f_274_, 2, v_inst_264_);
        crate::leanh::lean_closure_set(v___f_274_, 3, v_declName_265_);
        v___x_275_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(
            v_inst_263_,
            v_inst_266_,
            v_selectionRangeStx_267_,
        );
        v___x_276_ = crate::leanh::lean_apply_4(
            v_map_272_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_273_,
            v___x_275_,
        );
        v___x_277_ = crate::leanh::lean_apply_4(
            v_toBind_268_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_276_,
            v___f_274_,
        );
        return v___x_277_;
    } else {
        let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_____x_270_);
        crate::leanh::lean_dec(v_toBind_268_);
        crate::leanh::lean_dec(v_inst_266_);
        crate::leanh::lean_dec(v_declName_265_);
        crate::leanh::lean_dec_ref(v_inst_264_);
        crate::leanh::lean_dec_ref(v_inst_263_);
        crate::leanh::lean_dec_ref(v_toFunctor_262_);
        v___x_278_ = crate::leanh::lean_box(0);
        v___x_279_ =
            crate::leanh::lean_apply_2(v_toPure_269_, crate::leanh::lean_box(0), v___x_278_);
        return v___x_279_;
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed(
    mut v_toFunctor_280_: *mut crate::leanh::LeanObject,
    mut v_inst_281_: *mut crate::leanh::LeanObject,
    mut v_inst_282_: *mut crate::leanh::LeanObject,
    mut v_declName_283_: *mut crate::leanh::LeanObject,
    mut v_inst_284_: *mut crate::leanh::LeanObject,
    mut v_selectionRangeStx_285_: *mut crate::leanh::LeanObject,
    mut v_toBind_286_: *mut crate::leanh::LeanObject,
    mut v_toPure_287_: *mut crate::leanh::LeanObject,
    mut v_____x_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_selectionRangeStx_285_);
    return v_res_289_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(
    mut v_inst_290_: *mut crate::leanh::LeanObject,
    mut v_inst_291_: *mut crate::leanh::LeanObject,
    mut v_inst_292_: *mut crate::leanh::LeanObject,
    mut v_declName_293_: *mut crate::leanh::LeanObject,
    mut v_rangeStx_294_: *mut crate::leanh::LeanObject,
    mut v_selectionRangeStx_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_296_ = crate::leanh::lean_ctor_get(v_inst_290_, 0);
    v_toBind_297_ = crate::leanh::lean_ctor_get(v_inst_290_, 1);
    crate::leanh::lean_inc_n(v_toBind_297_, 2);
    v_toFunctor_298_ = crate::leanh::lean_ctor_get(v_toApplicative_296_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_298_);
    v_toPure_299_ = crate::leanh::lean_ctor_get(v_toApplicative_296_, 1);
    crate::leanh::lean_inc(v_toPure_299_);
    crate::leanh::lean_inc(v_inst_292_);
    crate::leanh::lean_inc_ref(v_inst_290_);
    v___x_300_ =
        l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_290_, v_inst_292_, v_rangeStx_294_);
    v___f_301_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_301_, 0, v_toFunctor_298_);
    crate::leanh::lean_closure_set(v___f_301_, 1, v_inst_290_);
    crate::leanh::lean_closure_set(v___f_301_, 2, v_inst_291_);
    crate::leanh::lean_closure_set(v___f_301_, 3, v_declName_293_);
    crate::leanh::lean_closure_set(v___f_301_, 4, v_inst_292_);
    crate::leanh::lean_closure_set(v___f_301_, 5, v_selectionRangeStx_295_);
    crate::leanh::lean_closure_set(v___f_301_, 6, v_toBind_297_);
    crate::leanh::lean_closure_set(v___f_301_, 7, v_toPure_299_);
    v___x_302_ = crate::leanh::lean_apply_4(
        v_toBind_297_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_300_,
        v___f_301_,
    );
    return v___x_302_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___boxed(
    mut v_inst_303_: *mut crate::leanh::LeanObject,
    mut v_inst_304_: *mut crate::leanh::LeanObject,
    mut v_inst_305_: *mut crate::leanh::LeanObject,
    mut v_declName_306_: *mut crate::leanh::LeanObject,
    mut v_rangeStx_307_: *mut crate::leanh::LeanObject,
    mut v_selectionRangeStx_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_309_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(
        v_inst_303_,
        v_inst_304_,
        v_inst_305_,
        v_declName_306_,
        v_rangeStx_307_,
        v_selectionRangeStx_308_,
    );
    crate::leanh::lean_dec(v_rangeStx_307_);
    return v_res_309_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax(
    mut v_m_310_: *mut crate::leanh::LeanObject,
    mut v_inst_311_: *mut crate::leanh::LeanObject,
    mut v_inst_312_: *mut crate::leanh::LeanObject,
    mut v_inst_313_: *mut crate::leanh::LeanObject,
    mut v_declName_314_: *mut crate::leanh::LeanObject,
    mut v_rangeStx_315_: *mut crate::leanh::LeanObject,
    mut v_selectionRangeStx_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_318_: *mut crate::leanh::LeanObject,
    mut v_inst_319_: *mut crate::leanh::LeanObject,
    mut v_inst_320_: *mut crate::leanh::LeanObject,
    mut v_inst_321_: *mut crate::leanh::LeanObject,
    mut v_declName_322_: *mut crate::leanh::LeanObject,
    mut v_rangeStx_323_: *mut crate::leanh::LeanObject,
    mut v_selectionRangeStx_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_325_ = l_Lean_Elab_addDeclarationRangesFromSyntax(
        v_m_318_,
        v_inst_319_,
        v_inst_320_,
        v_inst_321_,
        v_declName_322_,
        v_rangeStx_323_,
        v_selectionRangeStx_324_,
    );
    crate::leanh::lean_dec(v_rangeStx_323_);
    return v_res_325_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(
    mut v_inst_335_: *mut crate::leanh::LeanObject,
    mut v_inst_336_: *mut crate::leanh::LeanObject,
    mut v_inst_337_: *mut crate::leanh::LeanObject,
    mut v_declName_338_: *mut crate::leanh::LeanObject,
    mut v_modsStx_339_: *mut crate::leanh::LeanObject,
    mut v_declStx_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: u8 = 0;
    crate::leanh::lean_inc(v_declStx_340_);
    v___x_341_ = l_Lean_Syntax_getKind(v_declStx_340_);
    v___x_342_ = l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1;
    v___x_343_ = lean_name_eq(v___x_341_, v___x_342_);
    crate::leanh::lean_dec(v___x_341_);
    if v___x_343_ == 0 {
        let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_344_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_345_ = lean_mk_empty_array_with_capacity(v___x_344_);
        v___x_346_ = lean_array_push(v___x_345_, v_modsStx_339_);
        crate::leanh::lean_inc(v_declStx_340_);
        v___x_347_ = lean_array_push(v___x_346_, v_declStx_340_);
        v___x_348_ = l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3;
        v___x_349_ = crate::leanh::lean_box(2);
        v_stx_350_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v_stx_350_, 0, v___x_349_);
        crate::leanh::lean_ctor_set(v_stx_350_, 1, v___x_348_);
        crate::leanh::lean_ctor_set(v_stx_350_, 2, v___x_347_);
        v___x_351_ = l_Lean_Elab_getDeclarationSelectionRef(v_declStx_340_);
        v___x_352_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(
            v_inst_335_,
            v_inst_336_,
            v_inst_337_,
            v_declName_338_,
            v_stx_350_,
            v___x_351_,
        );
        crate::leanh::lean_dec_ref_known(v_stx_350_, 3);
        return v___x_352_;
    } else {
        let mut v_toApplicative_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_declStx_340_);
        crate::leanh::lean_dec(v_modsStx_339_);
        crate::leanh::lean_dec(v_declName_338_);
        crate::leanh::lean_dec(v_inst_337_);
        crate::leanh::lean_dec_ref(v_inst_336_);
        v_toApplicative_353_ = crate::leanh::lean_ctor_get(v_inst_335_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_353_);
        crate::leanh::lean_dec_ref(v_inst_335_);
        v_toPure_354_ = crate::leanh::lean_ctor_get(v_toApplicative_353_, 1);
        crate::leanh::lean_inc(v_toPure_354_);
        crate::leanh::lean_dec_ref(v_toApplicative_353_);
        v___x_355_ = crate::leanh::lean_box(0);
        v___x_356_ =
            crate::leanh::lean_apply_2(v_toPure_354_, crate::leanh::lean_box(0), v___x_355_);
        return v___x_356_;
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesForBuiltin(
    mut v_m_357_: *mut crate::leanh::LeanObject,
    mut v_inst_358_: *mut crate::leanh::LeanObject,
    mut v_inst_359_: *mut crate::leanh::LeanObject,
    mut v_inst_360_: *mut crate::leanh::LeanObject,
    mut v_declName_361_: *mut crate::leanh::LeanObject,
    mut v_modsStx_362_: *mut crate::leanh::LeanObject,
    mut v_declStx_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Lean_Elab_DeclarationRange(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeclarationRange(
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
pub unsafe fn initialize_Lean_Elab_DeclarationRange(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DeclarationRange(builtin);
}
