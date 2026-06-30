// Lean compiler output
// Module: Init.Data.List.SplitOn.Basic
// Imports: Init.Data.List.Basic Init.NotationExtra Init.Data.Array.Bootstrap Init.Data.List.Lemmas
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_nat_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold;
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::List::Basic::{
    initialize_Init_Data_List_Basic, runtime_initialize_Init_Data_List_Basic,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11_value
) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0(
    mut v_x1_127_: *mut leanh::LeanObject,
    mut v_x2_128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_129_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_129_, 0, v_x1_127_);
    leanh::lean_ctor_set(v___x_129_, 1, v_x2_128_);
    return v___x_129_;
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
    mut v_p_152_: *mut leanh::LeanObject,
    mut v_a_153_: *mut leanh::LeanObject,
    mut v_a_154_: *mut leanh::LeanObject,
    mut v_a_155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: u8 = 0;
    let mut v___f_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: usize = 0;
    let mut v___x_165_: usize = 0;
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: u8 = 0;
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_153_) == 0 {
                    leanh::lean_dec_ref(v_p_152_);
                    v___x_156_ = lean_array_to_list(v_a_154_);
                    v___x_157_ = leanh::lean_box(0);
                    v___x_158_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_158_, 0, v___x_156_);
                    leanh::lean_ctor_set(v___x_158_, 1, v___x_157_);
                    v___x_159_ = lean_array_get_size(v_a_155_);
                    v___x_160_ = leanh::lean_unsigned_to_nat(0);
                    v___x_161_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9;
                    v___x_162_ = lean_nat_dec_lt(v___x_160_, v___x_159_);
                    if v___x_162_ == 0 {
                        leanh::lean_dec_ref(v_a_155_);
                        return v___x_158_;
                    } else {
                        v___f_163_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10;
                        v___x_164_ = lean_usize_of_nat(v___x_159_);
                        v___x_165_ = 0usize;
                        v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_161_,
                            v___f_163_,
                            v_a_155_,
                            v___x_164_,
                            v___x_165_,
                            v___x_158_,
                        );
                        return v___x_166_;
                    }
                } else {
                    v_head_167_ = leanh::lean_ctor_get(v_a_153_, 0);
                    leanh::lean_inc_n(v_head_167_, 2);
                    v_tail_168_ = leanh::lean_ctor_get(v_a_153_, 1);
                    leanh::lean_inc(v_tail_168_);
                    leanh::lean_dec_ref_known(v_a_153_, 2);
                    leanh::lean_inc_ref(v_p_152_);
                    v___x_169_ = leanh::lean_apply_1(v_p_152_, v_head_167_);
                    v___x_170_ = (leanh::lean_unbox(v___x_169_) as u8);
                    if v___x_170_ == 0 {
                        v___x_171_ = lean_array_push(v_a_154_, v_head_167_);
                        v_a_153_ = v_tail_168_;
                        v_a_154_ = v___x_171_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_head_167_);
                        v___x_173_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
                        v___x_174_ = lean_array_to_list(v_a_154_);
                        v___x_175_ = lean_array_push(v_a_155_, v___x_174_);
                        v_a_153_ = v_tail_168_;
                        v_a_154_ = v___x_173_;
                        v_a_155_ = v___x_175_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go(
    mut v_00_u03b1_177_: *mut leanh::LeanObject,
    mut v_p_178_: *mut leanh::LeanObject,
    mut v_a_179_: *mut leanh::LeanObject,
    mut v_a_180_: *mut leanh::LeanObject,
    mut v_a_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v_p_178_, v_a_179_, v_a_180_, v_a_181_,
    );
    return v___x_182_;
}
pub unsafe fn l_List_splitOnPTR___redArg(
    mut v_p_183_: *mut leanh::LeanObject,
    mut v_l_184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ =
        l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
    v___x_186_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v_p_183_, v_l_184_, v___x_185_, v___x_185_,
    );
    return v___x_186_;
}
pub unsafe fn l_List_splitOnPTR(
    mut v_00_u03b1_187_: *mut leanh::LeanObject,
    mut v_p_188_: *mut leanh::LeanObject,
    mut v_l_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_190_ =
        l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
    v___x_191_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v_p_188_, v_l_189_, v___x_190_, v___x_190_,
    );
    return v___x_191_;
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter___redArg(
    mut v_x_192_: *mut leanh::LeanObject,
    mut v_x_193_: *mut leanh::LeanObject,
    mut v_h__1_194_: *mut leanh::LeanObject,
    mut v_h__2_195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_192_) == 0 {
        let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_195_);
        v___x_196_ = leanh::lean_apply_1(v_h__1_194_, v_x_193_);
        return v___x_196_;
    } else {
        let mut v_head_197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_194_);
        v_head_197_ = leanh::lean_ctor_get(v_x_192_, 0);
        leanh::lean_inc(v_head_197_);
        v_tail_198_ = leanh::lean_ctor_get(v_x_192_, 1);
        leanh::lean_inc(v_tail_198_);
        leanh::lean_dec_ref_known(v_x_192_, 2);
        v___x_199_ = leanh::lean_apply_3(v_h__2_195_, v_head_197_, v_tail_198_, v_x_193_);
        return v___x_199_;
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter(
    mut v_00_u03b1_200_: *mut leanh::LeanObject,
    mut v_motive_201_: *mut leanh::LeanObject,
    mut v_x_202_: *mut leanh::LeanObject,
    mut v_x_203_: *mut leanh::LeanObject,
    mut v_h__1_204_: *mut leanh::LeanObject,
    mut v_h__2_205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_202_) == 0 {
        let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_205_);
        v___x_206_ = leanh::lean_apply_1(v_h__1_204_, v_x_203_);
        return v___x_206_;
    } else {
        let mut v_head_207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_204_);
        v_head_207_ = leanh::lean_ctor_get(v_x_202_, 0);
        leanh::lean_inc(v_head_207_);
        v_tail_208_ = leanh::lean_ctor_get(v_x_202_, 1);
        leanh::lean_inc(v_tail_208_);
        leanh::lean_dec_ref_known(v_x_202_, 2);
        v___x_209_ = leanh::lean_apply_3(v_h__2_205_, v_head_207_, v_tail_208_, v_x_203_);
        return v___x_209_;
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter___redArg(
    mut v_x_210_: *mut leanh::LeanObject,
    mut v_x_211_: *mut leanh::LeanObject,
    mut v_x_212_: *mut leanh::LeanObject,
    mut v_h__1_213_: *mut leanh::LeanObject,
    mut v_h__2_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_210_) == 0 {
        let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_214_);
        v___x_215_ = leanh::lean_apply_2(v_h__1_213_, v_x_211_, v_x_212_);
        return v___x_215_;
    } else {
        let mut v_head_216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_213_);
        v_head_216_ = leanh::lean_ctor_get(v_x_210_, 0);
        leanh::lean_inc(v_head_216_);
        v_tail_217_ = leanh::lean_ctor_get(v_x_210_, 1);
        leanh::lean_inc(v_tail_217_);
        leanh::lean_dec_ref_known(v_x_210_, 2);
        v___x_218_ =
            leanh::lean_apply_4(v_h__2_214_, v_head_216_, v_tail_217_, v_x_211_, v_x_212_);
        return v___x_218_;
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter(
    mut v_00_u03b1_219_: *mut leanh::LeanObject,
    mut v_motive_220_: *mut leanh::LeanObject,
    mut v_x_221_: *mut leanh::LeanObject,
    mut v_x_222_: *mut leanh::LeanObject,
    mut v_x_223_: *mut leanh::LeanObject,
    mut v_h__1_224_: *mut leanh::LeanObject,
    mut v_h__2_225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_221_) == 0 {
        let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_225_);
        v___x_226_ = leanh::lean_apply_2(v_h__1_224_, v_x_222_, v_x_223_);
        return v___x_226_;
    } else {
        let mut v_head_227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_224_);
        v_head_227_ = leanh::lean_ctor_get(v_x_221_, 0);
        leanh::lean_inc(v_head_227_);
        v_tail_228_ = leanh::lean_ctor_get(v_x_221_, 1);
        leanh::lean_inc(v_tail_228_);
        leanh::lean_dec_ref_known(v_x_221_, 2);
        v___x_229_ =
            leanh::lean_apply_4(v_h__2_225_, v_head_227_, v_tail_228_, v_x_222_, v_x_223_);
        return v___x_229_;
    }
}
pub unsafe fn l_List_splitOn___redArg___lam__0(
    mut v_inst_230_: *mut leanh::LeanObject,
    mut v_a_231_: *mut leanh::LeanObject,
    mut v_x_232_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: u8 = 0;
    v___x_233_ = leanh::lean_apply_2(v_inst_230_, v_x_232_, v_a_231_);
    v___x_234_ = (leanh::lean_unbox(v___x_233_) as u8);
    return v___x_234_;
}
pub unsafe fn l_List_splitOn___redArg___lam__0___boxed(
    mut v_inst_235_: *mut leanh::LeanObject,
    mut v_a_236_: *mut leanh::LeanObject,
    mut v_x_237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_238_: u8 = 0;
    let mut v_r_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_238_ = l_List_splitOn___redArg___lam__0(v_inst_235_, v_a_236_, v_x_237_);
    v_r_239_ = leanh::lean_box((v_res_238_) as usize);
    return v_r_239_;
}
pub unsafe fn l_List_splitOn___redArg(
    mut v_inst_240_: *mut leanh::LeanObject,
    mut v_a_241_: *mut leanh::LeanObject,
    mut v_as_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_243_ = leanh::lean_alloc_closure(
        l_List_splitOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_243_, 0, v_inst_240_);
    leanh::lean_closure_set(v___f_243_, 1, v_a_241_);
    v___x_244_ =
        l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
    v___x_245_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v___f_243_, v_as_242_, v___x_244_, v___x_244_,
    );
    return v___x_245_;
}
pub unsafe fn l_List_splitOn(
    mut v_00_u03b1_246_: *mut leanh::LeanObject,
    mut v_inst_247_: *mut leanh::LeanObject,
    mut v_a_248_: *mut leanh::LeanObject,
    mut v_as_249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_250_ = leanh::lean_alloc_closure(
        l_List_splitOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_250_, 0, v_inst_247_);
    leanh::lean_closure_set(v___f_250_, 1, v_a_248_);
    v___x_251_ =
        l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
    v___x_252_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v___f_250_, v_as_249_, v___x_251_, v___x_251_,
    );
    return v___x_252_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_SplitOn_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_SplitOn_Basic(
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
pub unsafe fn initialize_Init_Data_List_SplitOn_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_SplitOn_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_SplitOn_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_SplitOn_Basic(builtin);
}