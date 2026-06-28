// Lean compiler output
// Module: Lean.Elab.Tactic.ExposeNames
// Imports: Lean.Meta.Tactic.ExposeNames Lean.Elab.Tactic.Basic
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr4;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Tactic::ExposeNames::{
    initialize_Lean_Meta_Tactic_ExposeNames, l_Lean_MVarId_exposeNames,
    runtime_initialize_Lean_Meta_Tactic_ExposeNames,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Lean_Elab_Tactic_evalExposeNames___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalExposeNames___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExposeNames___redArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 111, 115, 101, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3_value) as *mut LeanObject,11647286487098892037 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 69, 120, 112, 111, 115, 101, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6_value) as *mut LeanObject,15363610956975313185 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0(
    mut v___y_111_: *mut LeanObject,
    mut v___y_112_: *mut LeanObject,
    mut v___y_113_: *mut LeanObject,
    mut v___y_114_: *mut LeanObject,
    mut v___y_115_: *mut LeanObject,
    mut v___y_116_: *mut LeanObject,
    mut v___y_117_: *mut LeanObject,
    mut v___y_118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_130_: u8 = 0;
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_134_: u8 = 0;
    let mut v_a_135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_138_: u8 = 0;
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_120_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_112_, v___y_115_, v___y_116_, v___y_117_, v___y_118_,
                );
                if lean_obj_tag(v___x_120_) == 0 {
                    v_a_121_ = lean_ctor_get(v___x_120_, 0);
                    lean_inc(v_a_121_);
                    lean_dec_ref_known(v___x_120_, 1);
                    v___x_122_ = l_Lean_MVarId_exposeNames(
                        v_a_121_, v___y_115_, v___y_116_, v___y_117_, v___y_118_,
                    );
                    if lean_obj_tag(v___x_122_) == 0 {
                        v_a_123_ = lean_ctor_get(v___x_122_, 0);
                        lean_inc(v_a_123_);
                        lean_dec_ref_known(v___x_122_, 1);
                        v___x_124_ = lean_box(0);
                        v___x_125_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_125_, 0, v_a_123_);
                        lean_ctor_set(v___x_125_, 1, v___x_124_);
                        v___x_126_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_125_, v___y_112_, v___y_115_, v___y_116_, v___y_117_, v___y_118_,
                        );
                        return v___x_126_;
                    } else {
                        v_a_127_ = lean_ctor_get(v___x_122_, 0);
                        v_isSharedCheck_134_ = (!lean_is_exclusive(v___x_122_)) as u8;
                        if v_isSharedCheck_134_ == 0 {
                            v___x_129_ = v___x_122_;
                            v_isShared_130_ = v_isSharedCheck_134_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_127_);
                            lean_dec(v___x_122_);
                            v___x_129_ = lean_box(0);
                            v_isShared_130_ = v_isSharedCheck_134_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_135_ = lean_ctor_get(v___x_120_, 0);
                    v_isSharedCheck_142_ = (!lean_is_exclusive(v___x_120_)) as u8;
                    if v_isSharedCheck_142_ == 0 {
                        v___x_137_ = v___x_120_;
                        v_isShared_138_ = v_isSharedCheck_142_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_135_);
                        lean_dec(v___x_120_);
                        v___x_137_ = lean_box(0);
                        v_isShared_138_ = v_isSharedCheck_142_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_130_ == 0 {
                    v___x_132_ = v___x_129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
                    v___x_132_ = v_reuseFailAlloc_133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_132_;
            }
            3 => {
                if v_isShared_138_ == 0 {
                    v___x_140_ = v___x_137_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
                    v___x_140_ = v_reuseFailAlloc_141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0___boxed(
    mut v___y_143_: *mut LeanObject,
    mut v___y_144_: *mut LeanObject,
    mut v___y_145_: *mut LeanObject,
    mut v___y_146_: *mut LeanObject,
    mut v___y_147_: *mut LeanObject,
    mut v___y_148_: *mut LeanObject,
    mut v___y_149_: *mut LeanObject,
    mut v___y_150_: *mut LeanObject,
    mut v___y_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_152_: *mut LeanObject = core::ptr::null_mut();
    v_res_152_ = l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0(
        v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_,
        v___y_150_,
    );
    lean_dec(v___y_150_);
    lean_dec_ref(v___y_149_);
    lean_dec(v___y_148_);
    lean_dec_ref(v___y_147_);
    lean_dec(v___y_146_);
    lean_dec_ref(v___y_145_);
    lean_dec(v___y_144_);
    lean_dec_ref(v___y_143_);
    return v_res_152_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___redArg(
    mut v_a_154_: *mut LeanObject,
    mut v_a_155_: *mut LeanObject,
    mut v_a_156_: *mut LeanObject,
    mut v_a_157_: *mut LeanObject,
    mut v_a_158_: *mut LeanObject,
    mut v_a_159_: *mut LeanObject,
    mut v_a_160_: *mut LeanObject,
    mut v_a_161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    v___f_163_ = l_Lean_Elab_Tactic_evalExposeNames___redArg___closed__0;
    v___x_164_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_163_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_,
    );
    return v___x_164_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___redArg___boxed(
    mut v_a_165_: *mut LeanObject,
    mut v_a_166_: *mut LeanObject,
    mut v_a_167_: *mut LeanObject,
    mut v_a_168_: *mut LeanObject,
    mut v_a_169_: *mut LeanObject,
    mut v_a_170_: *mut LeanObject,
    mut v_a_171_: *mut LeanObject,
    mut v_a_172_: *mut LeanObject,
    mut v_a_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_174_: *mut LeanObject = core::ptr::null_mut();
    v_res_174_ = l_Lean_Elab_Tactic_evalExposeNames___redArg(
        v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_,
    );
    lean_dec(v_a_172_);
    lean_dec_ref(v_a_171_);
    lean_dec(v_a_170_);
    lean_dec_ref(v_a_169_);
    lean_dec(v_a_168_);
    lean_dec_ref(v_a_167_);
    lean_dec(v_a_166_);
    lean_dec_ref(v_a_165_);
    return v_res_174_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames(
    mut v_x_175_: *mut LeanObject,
    mut v_a_176_: *mut LeanObject,
    mut v_a_177_: *mut LeanObject,
    mut v_a_178_: *mut LeanObject,
    mut v_a_179_: *mut LeanObject,
    mut v_a_180_: *mut LeanObject,
    mut v_a_181_: *mut LeanObject,
    mut v_a_182_: *mut LeanObject,
    mut v_a_183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    v___x_185_ = l_Lean_Elab_Tactic_evalExposeNames___redArg(
        v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_,
    );
    return v___x_185_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___boxed(
    mut v_x_186_: *mut LeanObject,
    mut v_a_187_: *mut LeanObject,
    mut v_a_188_: *mut LeanObject,
    mut v_a_189_: *mut LeanObject,
    mut v_a_190_: *mut LeanObject,
    mut v_a_191_: *mut LeanObject,
    mut v_a_192_: *mut LeanObject,
    mut v_a_193_: *mut LeanObject,
    mut v_a_194_: *mut LeanObject,
    mut v_a_195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_196_: *mut LeanObject = core::ptr::null_mut();
    v_res_196_ = l_Lean_Elab_Tactic_evalExposeNames(
        v_x_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_,
    );
    lean_dec(v_a_194_);
    lean_dec_ref(v_a_193_);
    lean_dec(v_a_192_);
    lean_dec_ref(v_a_191_);
    lean_dec(v_a_190_);
    lean_dec_ref(v_a_189_);
    lean_dec(v_a_188_);
    lean_dec_ref(v_a_187_);
    lean_dec(v_x_186_);
    return v_res_196_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1()
-> *mut LeanObject {
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    v___x_214_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_215_ = l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4;
    v___x_216_ = l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7;
    v___x_217_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalExposeNames___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_218_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_214_, v___x_215_, v___x_216_, v___x_217_,
    );
    return v___x_218_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___boxed(
    mut v_a_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_220_: *mut LeanObject = core::ptr::null_mut();
    v_res_220_ = l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1();
    return v_res_220_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_ExposeNames(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_ExposeNames(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_ExposeNames(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ExposeNames(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_ExposeNames(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_ExposeNames(builtin);
}
