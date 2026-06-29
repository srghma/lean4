// Lean compiler output
// Module: Lean.DocString
// Imports: Lean.DocString.Extension Lean.DocString.Links Lean.Parser.Tactic.Doc Lean.Parser.Term.Doc
use crate::ffi::lean_string_append;
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
pub unsafe fn l_Lean_findDocString_x3f(
    mut v_env_38_: *mut crate::leanh::LeanObject,
    mut v_declName_39_: *mut crate::leanh::LeanObject,
    mut v_includeBuiltin_40_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exts_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spellings_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_50_: u8 = 0;
    let mut v_val_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_54_: u8 = 0;
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_64_: u8 = 0;
    let mut v_isSharedCheck_65_: u8 = 0;
    let mut v_unused_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_39_);
                crate::leanh::lean_inc_ref(v_env_38_);
                v___x_67_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_38_, v_declName_39_);
                if crate::leanh::lean_obj_tag(v___x_67_) == 0 {
                    v___y_43_ = v_declName_39_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_39_);
                    v_val_68_ = crate::leanh::lean_ctor_get(v___x_67_, 0);
                    crate::leanh::lean_inc(v_val_68_);
                    crate::leanh::lean_dec_ref_known(v___x_67_, 1);
                    v___y_43_ = v_val_68_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v___y_43_, 2);
                crate::leanh::lean_inc_ref_n(v_env_38_, 2);
                v_exts_44_ =
                    l_Lean_Parser_Tactic_Doc_getTacticExtensionString(v_env_38_, v___y_43_);
                v_spellings_45_ =
                    l_Lean_Parser_Term_Doc_getRecommendedSpellingString(v_env_38_, v___y_43_);
                v___x_46_ =
                    l_Lean_findSimpleDocString_x3f(v_env_38_, v___y_43_, v_includeBuiltin_40_);
                if crate::leanh::lean_obj_tag(v___x_46_) == 0 {
                    v_a_47_ = crate::leanh::lean_ctor_get(v___x_46_, 0);
                    crate::leanh::lean_inc(v_a_47_);
                    if crate::leanh::lean_obj_tag(v_a_47_) == 0 {
                        crate::leanh::lean_dec_ref(v_spellings_45_);
                        crate::leanh::lean_dec_ref(v_exts_44_);
                        return v___x_46_;
                    } else {
                        v_isSharedCheck_65_ = (!crate::leanh::lean_is_exclusive(v___x_46_)) as u8;
                        if v_isSharedCheck_65_ == 0 {
                            v_unused_66_ = crate::leanh::lean_ctor_get(v___x_46_, 0);
                            crate::leanh::lean_dec(v_unused_66_);
                            v___x_49_ = v___x_46_;
                            v_isShared_50_ = v_isSharedCheck_65_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_46_);
                            v___x_49_ = crate::leanh::lean_box(0);
                            v_isShared_50_ = v_isSharedCheck_65_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_spellings_45_);
                    crate::leanh::lean_dec_ref(v_exts_44_);
                    return v___x_46_;
                }
            }
            2 => {
                v_val_51_ = crate::leanh::lean_ctor_get(v_a_47_, 0);
                v_isSharedCheck_64_ = (!crate::leanh::lean_is_exclusive(v_a_47_)) as u8;
                if v_isSharedCheck_64_ == 0 {
                    v___x_53_ = v_a_47_;
                    v_isShared_54_ = v_isSharedCheck_64_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_51_);
                    crate::leanh::lean_dec(v_a_47_);
                    v___x_53_ = crate::leanh::lean_box(0);
                    v_isShared_54_ = v_isSharedCheck_64_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_55_ = lean_string_append(v_val_51_, v_exts_44_);
                crate::leanh::lean_dec_ref(v_exts_44_);
                v___x_56_ = lean_string_append(v___x_55_, v_spellings_45_);
                crate::leanh::lean_dec_ref(v_spellings_45_);
                v___x_57_ = l_Lean_rewriteManualLinks(v___x_56_);
                if v_isShared_54_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_53_, 0, v___x_57_);
                    v___x_59_ = v___x_53_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_63_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_57_);
                    v___x_59_ = v_reuseFailAlloc_63_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_50_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_49_, 0, v___x_59_);
                    v___x_61_ = v___x_49_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_62_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
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
    mut v_env_69_: *mut crate::leanh::LeanObject,
    mut v_declName_70_: *mut crate::leanh::LeanObject,
    mut v_includeBuiltin_71_: *mut crate::leanh::LeanObject,
    mut v_a_72_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeBuiltin_boxed_73_: u8 = 0;
    let mut v_res_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeBuiltin_boxed_73_ = (crate::leanh::lean_unbox(v_includeBuiltin_71_) as u8);
    v_res_74_ = l_Lean_findDocString_x3f(v_env_69_, v_declName_70_, v_includeBuiltin_boxed_73_);
    return v_res_74_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_DocString_Extension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Links(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Term_Doc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DocString(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_DocString_Extension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString_Links(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Tactic_Doc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Term_Doc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DocString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_DocString(builtin);
}
