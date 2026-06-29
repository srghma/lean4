// Lean compiler output
// Module: Lean.Elab.Tactic.ExposeNames
// Imports: Lean.Meta.Tactic.ExposeNames Lean.Elab.Tactic.Basic
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
pub static l_Lean_Elab_Tactic_evalExposeNames___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_evalExposeNames___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExposeNames___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 111, 115, 101, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3_value) as *mut crate::leanh::LeanObject,11647286487098892037 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 69, 120, 112, 111, 115, 101, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6_value) as *mut crate::leanh::LeanObject,15363610956975313185 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0(
    mut v___y_111_: *mut crate::leanh::LeanObject,
    mut v___y_112_: *mut crate::leanh::LeanObject,
    mut v___y_113_: *mut crate::leanh::LeanObject,
    mut v___y_114_: *mut crate::leanh::LeanObject,
    mut v___y_115_: *mut crate::leanh::LeanObject,
    mut v___y_116_: *mut crate::leanh::LeanObject,
    mut v___y_117_: *mut crate::leanh::LeanObject,
    mut v___y_118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_130_: u8 = 0;
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_134_: u8 = 0;
    let mut v_a_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_138_: u8 = 0;
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_120_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_112_, v___y_115_, v___y_116_, v___y_117_, v___y_118_,
                );
                if crate::leanh::lean_obj_tag(v___x_120_) == 0 {
                    v_a_121_ = crate::leanh::lean_ctor_get(v___x_120_, 0);
                    crate::leanh::lean_inc(v_a_121_);
                    crate::leanh::lean_dec_ref_known(v___x_120_, 1);
                    v___x_122_ = l_Lean_MVarId_exposeNames(
                        v_a_121_, v___y_115_, v___y_116_, v___y_117_, v___y_118_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_122_) == 0 {
                        v_a_123_ = crate::leanh::lean_ctor_get(v___x_122_, 0);
                        crate::leanh::lean_inc(v_a_123_);
                        crate::leanh::lean_dec_ref_known(v___x_122_, 1);
                        v___x_124_ = crate::leanh::lean_box(0);
                        v___x_125_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_125_, 0, v_a_123_);
                        crate::leanh::lean_ctor_set(v___x_125_, 1, v___x_124_);
                        v___x_126_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_125_, v___y_112_, v___y_115_, v___y_116_, v___y_117_, v___y_118_,
                        );
                        return v___x_126_;
                    } else {
                        v_a_127_ = crate::leanh::lean_ctor_get(v___x_122_, 0);
                        v_isSharedCheck_134_ = (!crate::leanh::lean_is_exclusive(v___x_122_)) as u8;
                        if v_isSharedCheck_134_ == 0 {
                            v___x_129_ = v___x_122_;
                            v_isShared_130_ = v_isSharedCheck_134_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_127_);
                            crate::leanh::lean_dec(v___x_122_);
                            v___x_129_ = crate::leanh::lean_box(0);
                            v_isShared_130_ = v_isSharedCheck_134_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_135_ = crate::leanh::lean_ctor_get(v___x_120_, 0);
                    v_isSharedCheck_142_ = (!crate::leanh::lean_is_exclusive(v___x_120_)) as u8;
                    if v_isSharedCheck_142_ == 0 {
                        v___x_137_ = v___x_120_;
                        v_isShared_138_ = v_isSharedCheck_142_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_135_);
                        crate::leanh::lean_dec(v___x_120_);
                        v___x_137_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
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
                    v_reuseFailAlloc_141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
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
    mut v___y_143_: *mut crate::leanh::LeanObject,
    mut v___y_144_: *mut crate::leanh::LeanObject,
    mut v___y_145_: *mut crate::leanh::LeanObject,
    mut v___y_146_: *mut crate::leanh::LeanObject,
    mut v___y_147_: *mut crate::leanh::LeanObject,
    mut v___y_148_: *mut crate::leanh::LeanObject,
    mut v___y_149_: *mut crate::leanh::LeanObject,
    mut v___y_150_: *mut crate::leanh::LeanObject,
    mut v___y_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0(
        v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_,
        v___y_150_,
    );
    crate::leanh::lean_dec(v___y_150_);
    crate::leanh::lean_dec_ref(v___y_149_);
    crate::leanh::lean_dec(v___y_148_);
    crate::leanh::lean_dec_ref(v___y_147_);
    crate::leanh::lean_dec(v___y_146_);
    crate::leanh::lean_dec_ref(v___y_145_);
    crate::leanh::lean_dec(v___y_144_);
    crate::leanh::lean_dec_ref(v___y_143_);
    return v_res_152_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___redArg(
    mut v_a_154_: *mut crate::leanh::LeanObject,
    mut v_a_155_: *mut crate::leanh::LeanObject,
    mut v_a_156_: *mut crate::leanh::LeanObject,
    mut v_a_157_: *mut crate::leanh::LeanObject,
    mut v_a_158_: *mut crate::leanh::LeanObject,
    mut v_a_159_: *mut crate::leanh::LeanObject,
    mut v_a_160_: *mut crate::leanh::LeanObject,
    mut v_a_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_163_ = l_Lean_Elab_Tactic_evalExposeNames___redArg___closed__0;
    v___x_164_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_163_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_,
    );
    return v___x_164_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___redArg___boxed(
    mut v_a_165_: *mut crate::leanh::LeanObject,
    mut v_a_166_: *mut crate::leanh::LeanObject,
    mut v_a_167_: *mut crate::leanh::LeanObject,
    mut v_a_168_: *mut crate::leanh::LeanObject,
    mut v_a_169_: *mut crate::leanh::LeanObject,
    mut v_a_170_: *mut crate::leanh::LeanObject,
    mut v_a_171_: *mut crate::leanh::LeanObject,
    mut v_a_172_: *mut crate::leanh::LeanObject,
    mut v_a_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_174_ = l_Lean_Elab_Tactic_evalExposeNames___redArg(
        v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_,
    );
    crate::leanh::lean_dec(v_a_172_);
    crate::leanh::lean_dec_ref(v_a_171_);
    crate::leanh::lean_dec(v_a_170_);
    crate::leanh::lean_dec_ref(v_a_169_);
    crate::leanh::lean_dec(v_a_168_);
    crate::leanh::lean_dec_ref(v_a_167_);
    crate::leanh::lean_dec(v_a_166_);
    crate::leanh::lean_dec_ref(v_a_165_);
    return v_res_174_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames(
    mut v_x_175_: *mut crate::leanh::LeanObject,
    mut v_a_176_: *mut crate::leanh::LeanObject,
    mut v_a_177_: *mut crate::leanh::LeanObject,
    mut v_a_178_: *mut crate::leanh::LeanObject,
    mut v_a_179_: *mut crate::leanh::LeanObject,
    mut v_a_180_: *mut crate::leanh::LeanObject,
    mut v_a_181_: *mut crate::leanh::LeanObject,
    mut v_a_182_: *mut crate::leanh::LeanObject,
    mut v_a_183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ = l_Lean_Elab_Tactic_evalExposeNames___redArg(
        v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_,
    );
    return v___x_185_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExposeNames___boxed(
    mut v_x_186_: *mut crate::leanh::LeanObject,
    mut v_a_187_: *mut crate::leanh::LeanObject,
    mut v_a_188_: *mut crate::leanh::LeanObject,
    mut v_a_189_: *mut crate::leanh::LeanObject,
    mut v_a_190_: *mut crate::leanh::LeanObject,
    mut v_a_191_: *mut crate::leanh::LeanObject,
    mut v_a_192_: *mut crate::leanh::LeanObject,
    mut v_a_193_: *mut crate::leanh::LeanObject,
    mut v_a_194_: *mut crate::leanh::LeanObject,
    mut v_a_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_196_ = l_Lean_Elab_Tactic_evalExposeNames(
        v_x_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_,
    );
    crate::leanh::lean_dec(v_a_194_);
    crate::leanh::lean_dec_ref(v_a_193_);
    crate::leanh::lean_dec(v_a_192_);
    crate::leanh::lean_dec_ref(v_a_191_);
    crate::leanh::lean_dec(v_a_190_);
    crate::leanh::lean_dec_ref(v_a_189_);
    crate::leanh::lean_dec(v_a_188_);
    crate::leanh::lean_dec_ref(v_a_187_);
    crate::leanh::lean_dec(v_x_186_);
    return v_res_196_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_215_ = l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4;
    v___x_216_ = l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7;
    v___x_217_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_220_ = l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1();
    return v_res_220_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_ExposeNames(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ExposeNames_0__Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_ExposeNames(
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
pub unsafe fn initialize_Lean_Elab_Tactic_ExposeNames(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ExposeNames(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_ExposeNames(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_ExposeNames(builtin);
}
