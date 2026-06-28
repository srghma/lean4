// Lean compiler output
// Module: Lean.DocString
// Imports: Lean.DocString.Extension Lean.DocString.Links Lean.Parser.Tactic.Doc Lean.Parser.Term.Doc
use crate::r#gen::Lean::DocString::Extension::{
    initialize_Lean_DocString_Extension, l_Lean_findSimpleDocString_x3f,
    runtime_initialize_Lean_DocString_Extension,
};
use crate::r#gen::Lean::DocString::Links::{
    initialize_Lean_DocString_Links, l_Lean_rewriteManualLinks,
    runtime_initialize_Lean_DocString_Links,
};
use crate::r#gen::Lean::Parser::Tactic::Doc::{
    initialize_Lean_Parser_Tactic_Doc, l_Lean_Parser_Tactic_Doc_alternativeOfTactic,
    l_Lean_Parser_Tactic_Doc_getTacticExtensionString, runtime_initialize_Lean_Parser_Tactic_Doc,
};
use crate::r#gen::Lean::Parser::Term::Doc::{
    initialize_Lean_Parser_Term_Doc, l_Lean_Parser_Term_Doc_getRecommendedSpellingString,
    runtime_initialize_Lean_Parser_Term_Doc,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub unsafe fn l_Lean_findDocString_x3f(
    mut v_env_38_: *mut LeanObject,
    mut v_declName_39_: *mut LeanObject,
    mut v_includeBuiltin_40_: u8,
) -> *mut LeanObject {
    let mut v___y_43_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exts_44_: *mut LeanObject = core::ptr::null_mut();
    let mut v_spellings_45_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_50_: u8 = 0;
    let mut v_val_51_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_54_: u8 = 0;
    let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_63_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_64_: u8 = 0;
    let mut v_isSharedCheck_65_: u8 = 0;
    let mut v_unused_66_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_68_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_39_);
                lean_inc_ref(v_env_38_);
                v___x_67_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_38_, v_declName_39_);
                if lean_obj_tag(v___x_67_) == 0 {
                    v___y_43_ = v_declName_39_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_declName_39_);
                    v_val_68_ = lean_ctor_get(v___x_67_, 0);
                    lean_inc(v_val_68_);
                    lean_dec_ref_known(v___x_67_, 1);
                    v___y_43_ = v_val_68_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v___y_43_, 2);
                lean_inc_ref_n(v_env_38_, 2);
                v_exts_44_ =
                    l_Lean_Parser_Tactic_Doc_getTacticExtensionString(v_env_38_, v___y_43_);
                v_spellings_45_ =
                    l_Lean_Parser_Term_Doc_getRecommendedSpellingString(v_env_38_, v___y_43_);
                v___x_46_ =
                    l_Lean_findSimpleDocString_x3f(v_env_38_, v___y_43_, v_includeBuiltin_40_);
                if lean_obj_tag(v___x_46_) == 0 {
                    v_a_47_ = lean_ctor_get(v___x_46_, 0);
                    lean_inc(v_a_47_);
                    if lean_obj_tag(v_a_47_) == 0 {
                        lean_dec_ref(v_spellings_45_);
                        lean_dec_ref(v_exts_44_);
                        return v___x_46_;
                    } else {
                        v_isSharedCheck_65_ = (!lean_is_exclusive(v___x_46_)) as u8;
                        if v_isSharedCheck_65_ == 0 {
                            v_unused_66_ = lean_ctor_get(v___x_46_, 0);
                            lean_dec(v_unused_66_);
                            v___x_49_ = v___x_46_;
                            v_isShared_50_ = v_isSharedCheck_65_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_46_);
                            v___x_49_ = lean_box(0);
                            v_isShared_50_ = v_isSharedCheck_65_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_spellings_45_);
                    lean_dec_ref(v_exts_44_);
                    return v___x_46_;
                }
            }
            2 => {
                v_val_51_ = lean_ctor_get(v_a_47_, 0);
                v_isSharedCheck_64_ = (!lean_is_exclusive(v_a_47_)) as u8;
                if v_isSharedCheck_64_ == 0 {
                    v___x_53_ = v_a_47_;
                    v_isShared_54_ = v_isSharedCheck_64_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_val_51_);
                    lean_dec(v_a_47_);
                    v___x_53_ = lean_box(0);
                    v_isShared_54_ = v_isSharedCheck_64_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_55_ = lean_string_append(v_val_51_, v_exts_44_);
                lean_dec_ref(v_exts_44_);
                v___x_56_ = lean_string_append(v___x_55_, v_spellings_45_);
                lean_dec_ref(v_spellings_45_);
                v___x_57_ = l_Lean_rewriteManualLinks(v___x_56_);
                if v_isShared_54_ == 0 {
                    lean_ctor_set(v___x_53_, 0, v___x_57_);
                    v___x_59_ = v___x_53_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_57_);
                    v___x_59_ = v_reuseFailAlloc_63_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_50_ == 0 {
                    lean_ctor_set(v___x_49_, 0, v___x_59_);
                    v___x_61_ = v___x_49_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
                    v___x_61_ = v_reuseFailAlloc_62_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_61_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findDocString_x3f___boxed(
    mut v_env_69_: *mut LeanObject,
    mut v_declName_70_: *mut LeanObject,
    mut v_includeBuiltin_71_: *mut LeanObject,
    mut v_a_72_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeBuiltin_boxed_73_: u8 = 0;
    let mut v_res_74_: *mut LeanObject = core::ptr::null_mut();
    v_includeBuiltin_boxed_73_ = (lean_unbox(v_includeBuiltin_71_) as u8);
    v_res_74_ = l_Lean_findDocString_x3f(v_env_69_, v_declName_70_, v_includeBuiltin_boxed_73_);
    return v_res_74_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_DocString_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Links(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Term_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DocString(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_DocString_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_DocString_Links(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Term_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_DocString(builtin);
}
