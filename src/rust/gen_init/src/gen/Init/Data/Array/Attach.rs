// Lean compiler output
// Module: Init.Data.Array.Attach
// Imports: Init.Data.List.Attach Init.Data.Array.Lemmas Init.Data.Array.Bootstrap Init.Data.Array.Count
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Count::{
    initialize_Init_Data_Array_Count, runtime_initialize_Init_Data_Array_Count,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::Attach::{
    initialize_Init_Data_List_Attach, runtime_initialize_Init_Data_List_Attach,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{lean_array_mk, lean_array_to_list};
pub static l_Array_pmapImpl___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_pmapImpl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_pmapImpl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_pmapImpl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_pmapImpl___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_pmapImpl___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_pmapImpl___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_pmapImpl___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_pmapImpl___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_pmapImpl___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_pmapImpl___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_pmapImpl___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_pmapImpl___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_List_mapTR_loop___at___00Array_pmap_spec__0___redArg(
    mut v_f_132_: *mut crate::leanh::LeanObject,
    mut v_a_133_: *mut crate::leanh::LeanObject,
    mut v_a_134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_140_: u8 = 0;
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_133_) == 0 {
                    crate::leanh::lean_dec(v_f_132_);
                    v___x_135_ = l_List_reverse___redArg(v_a_134_);
                    return v___x_135_;
                } else {
                    v_head_136_ = crate::leanh::lean_ctor_get(v_a_133_, 0);
                    v_tail_137_ = crate::leanh::lean_ctor_get(v_a_133_, 1);
                    v_isSharedCheck_146_ = (!crate::leanh::lean_is_exclusive(v_a_133_)) as u8;
                    if v_isSharedCheck_146_ == 0 {
                        v___x_139_ = v_a_133_;
                        v_isShared_140_ = v_isSharedCheck_146_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_137_);
                        crate::leanh::lean_inc(v_head_136_);
                        crate::leanh::lean_dec(v_a_133_);
                        v___x_139_ = crate::leanh::lean_box(0);
                        v_isShared_140_ = v_isSharedCheck_146_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_f_132_);
                v___x_141_ =
                    crate::leanh::lean_apply_2(v_f_132_, v_head_136_, crate::leanh::lean_box(0));
                if v_isShared_140_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_139_, 1, v_a_134_);
                    crate::leanh::lean_ctor_set(v___x_139_, 0, v___x_141_);
                    v___x_143_ = v___x_139_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_145_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_145_, 1, v_a_134_);
                    v___x_143_ = v_reuseFailAlloc_145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_133_ = v_tail_137_;
                v_a_134_ = v___x_143_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_pmap___redArg(
    mut v_f_147_: *mut crate::leanh::LeanObject,
    mut v_xs_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = lean_array_to_list(v_xs_148_);
    v___x_150_ = crate::leanh::lean_box(0);
    v___x_151_ =
        l_List_mapTR_loop___at___00Array_pmap_spec__0___redArg(v_f_147_, v___x_149_, v___x_150_);
    v___x_152_ = lean_array_mk(v___x_151_);
    return v___x_152_;
}
pub unsafe fn l_Array_pmap(
    mut v_00_u03b1_153_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_154_: *mut crate::leanh::LeanObject,
    mut v_P_155_: *mut crate::leanh::LeanObject,
    mut v_f_156_: *mut crate::leanh::LeanObject,
    mut v_xs_157_: *mut crate::leanh::LeanObject,
    mut v_H_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_159_ = l_Array_pmap___redArg(v_f_156_, v_xs_157_);
    return v___x_159_;
}
pub unsafe fn l_List_mapTR_loop___at___00Array_pmap_spec__0(
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_161_: *mut crate::leanh::LeanObject,
    mut v_f_162_: *mut crate::leanh::LeanObject,
    mut v_a_163_: *mut crate::leanh::LeanObject,
    mut v_a_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_165_ =
        l_List_mapTR_loop___at___00Array_pmap_spec__0___redArg(v_f_162_, v_a_163_, v_a_164_);
    return v___x_165_;
}
pub unsafe fn l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(
    mut v_xs_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_xs_166_);
    return v_xs_166_;
}
pub unsafe fn l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg___boxed(
    mut v_xs_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(v_xs_167_);
    crate::leanh::lean_dec_ref(v_xs_167_);
    return v_res_168_;
}
pub unsafe fn l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(
    mut v_00_u03b1_169_: *mut crate::leanh::LeanObject,
    mut v_xs_170_: *mut crate::leanh::LeanObject,
    mut v_P_171_: *mut crate::leanh::LeanObject,
    mut v_x_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_xs_170_);
    return v_xs_170_;
}
pub unsafe fn l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___boxed(
    mut v_00_u03b1_173_: *mut crate::leanh::LeanObject,
    mut v_xs_174_: *mut crate::leanh::LeanObject,
    mut v_P_175_: *mut crate::leanh::LeanObject,
    mut v_x_176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_177_ = l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(
        v_00_u03b1_173_,
        v_xs_174_,
        v_P_175_,
        v_x_176_,
    );
    crate::leanh::lean_dec_ref(v_xs_174_);
    return v_res_177_;
}
pub unsafe fn l_Array_attach___redArg(
    mut v_xs_178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_xs_178_);
    return v_xs_178_;
}
pub unsafe fn l_Array_attach___redArg___boxed(
    mut v_xs_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l_Array_attach___redArg(v_xs_179_);
    crate::leanh::lean_dec_ref(v_xs_179_);
    return v_res_180_;
}
pub unsafe fn l_Array_attach(
    mut v_00_u03b1_181_: *mut crate::leanh::LeanObject,
    mut v_xs_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_xs_182_);
    return v_xs_182_;
}
pub unsafe fn l_Array_attach___boxed(
    mut v_00_u03b1_183_: *mut crate::leanh::LeanObject,
    mut v_xs_184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_185_ = l_Array_attach(v_00_u03b1_183_, v_xs_184_);
    crate::leanh::lean_dec_ref(v_xs_184_);
    return v_res_185_;
}
pub unsafe fn l_Array_pmapImpl___redArg___lam__0(
    mut v_f_186_: *mut crate::leanh::LeanObject,
    mut v_x_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_188_ = crate::leanh::lean_apply_2(v_f_186_, v_x_187_, crate::leanh::lean_box(0));
    return v___x_188_;
}
pub unsafe fn l_Array_pmapImpl___redArg(
    mut v_f_208_: *mut crate::leanh::LeanObject,
    mut v_xs_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_212_: usize = 0;
    let mut v___x_213_: usize = 0;
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_210_ = crate::leanh::lean_alloc_closure(
        l_Array_pmapImpl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_210_, 0, v_f_208_);
    v___x_211_ = l_Array_pmapImpl___redArg___closed__9;
    v_sz_212_ = lean_array_size(v_xs_209_);
    v___x_213_ = 0usize;
    v___x_214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_211_,
        v___f_210_,
        v_sz_212_,
        v___x_213_,
        v_xs_209_,
    );
    return v___x_214_;
}
pub unsafe fn l_Array_pmapImpl(
    mut v_00_u03b1_215_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_216_: *mut crate::leanh::LeanObject,
    mut v_P_217_: *mut crate::leanh::LeanObject,
    mut v_f_218_: *mut crate::leanh::LeanObject,
    mut v_xs_219_: *mut crate::leanh::LeanObject,
    mut v_H_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_223_: usize = 0;
    let mut v___x_224_: usize = 0;
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_221_ = crate::leanh::lean_alloc_closure(
        l_Array_pmapImpl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_221_, 0, v_f_218_);
    v___x_222_ = l_Array_pmapImpl___redArg___closed__9;
    v_sz_223_ = lean_array_size(v_xs_219_);
    v___x_224_ = 0usize;
    v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_222_,
        v___f_221_,
        v_sz_223_,
        v___x_224_,
        v_xs_219_,
    );
    return v___x_225_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(
    mut v_sz_226_: usize,
    mut v_i_227_: usize,
    mut v_bs_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_229_: u8 = 0;
    let mut v_v_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: usize = 0;
    let mut v___x_234_: usize = 0;
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_229_ = lean_usize_dec_lt(v_i_227_, v_sz_226_);
                if v___x_229_ == 0 {
                    return v_bs_228_;
                } else {
                    v_v_230_ = lean_array_uget(v_bs_228_, v_i_227_);
                    v___x_231_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_232_ = lean_array_uset(v_bs_228_, v_i_227_, v___x_231_);
                    v___x_233_ = 1usize;
                    v___x_234_ = lean_usize_add(v_i_227_, v___x_233_);
                    v___x_235_ = lean_array_uset(v_bs_x27_232_, v_i_227_, v_v_230_);
                    v_i_227_ = v___x_234_;
                    v_bs_228_ = v___x_235_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg___boxed(
    mut v_sz_237_: *mut crate::leanh::LeanObject,
    mut v_i_238_: *mut crate::leanh::LeanObject,
    mut v_bs_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_240_: usize = 0;
    let mut v_i_boxed_241_: usize = 0;
    let mut v_res_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_240_ = crate::leanh::lean_unbox_usize(v_sz_237_);
    crate::leanh::lean_dec(v_sz_237_);
    v_i_boxed_241_ = crate::leanh::lean_unbox_usize(v_i_238_);
    crate::leanh::lean_dec(v_i_238_);
    v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_boxed_240_, v_i_boxed_241_, v_bs_239_);
    return v_res_242_;
}
pub unsafe fn l_Array_unattach___redArg(
    mut v_xs_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_244_: usize = 0;
    let mut v___x_245_: usize = 0;
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_244_ = lean_array_size(v_xs_243_);
    v___x_245_ = 0usize;
    v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_244_, v___x_245_, v_xs_243_);
    return v___x_246_;
}
pub unsafe fn l_Array_unattach(
    mut v_00_u03b1_247_: *mut crate::leanh::LeanObject,
    mut v_p_248_: *mut crate::leanh::LeanObject,
    mut v_xs_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_250_ = l_Array_unattach___redArg(v_xs_249_);
    return v___x_250_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0(
    mut v_00_u03b1_251_: *mut crate::leanh::LeanObject,
    mut v_sz_252_: usize,
    mut v_i_253_: usize,
    mut v_bs_254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_252_, v_i_253_, v_bs_254_);
    return v___x_255_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___boxed(
    mut v_00_u03b1_256_: *mut crate::leanh::LeanObject,
    mut v_sz_257_: *mut crate::leanh::LeanObject,
    mut v_i_258_: *mut crate::leanh::LeanObject,
    mut v_bs_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_260_: usize = 0;
    let mut v_i_boxed_261_: usize = 0;
    let mut v_res_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_260_ = crate::leanh::lean_unbox_usize(v_sz_257_);
    crate::leanh::lean_dec(v_sz_257_);
    v_i_boxed_261_ = crate::leanh::lean_unbox_usize(v_i_258_);
    crate::leanh::lean_dec(v_i_258_);
    v_res_262_ =
        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0(
            v_00_u03b1_256_,
            v_sz_boxed_260_,
            v_i_boxed_261_,
            v_bs_259_,
        );
    return v_res_262_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Attach(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Attach(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Attach(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Attach(builtin);
}
