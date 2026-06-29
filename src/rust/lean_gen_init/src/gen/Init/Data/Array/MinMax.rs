// Lean compiler output
// Module: Init.Data.Array.MinMax
// Imports: Init.Data.Array.Lemmas Init.Data.List.MinMax Init.Data.Order.Classes Init.Data.Array.Bootstrap Init.Data.Array.DecidableEq Init.Data.List.TakeDrop Init.Data.Order.Lemmas
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::DecidableEq::{
    initialize_Init_Data_Array_DecidableEq, runtime_initialize_Init_Data_Array_DecidableEq,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::MinMax::{
    initialize_Init_Data_List_MinMax, runtime_initialize_Init_Data_List_MinMax,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
};
pub static l_Array_min___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Array_min___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Array_min___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Array_min___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Array_min___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Array_min___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Array_min___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Array_min___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_min___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_min___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Array_min___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_min___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array_min___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_min___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_min___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Array_min___redArg___lam__0(
    mut v_inst_90_: *mut crate::leanh::LeanObject,
    mut v_x1_91_: *mut crate::leanh::LeanObject,
    mut v_x2_92_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_93_ = crate::leanh::lean_apply_2(v_inst_90_, v_x1_91_, v_x2_92_);
    return v___x_93_;
}
pub unsafe fn l_Array_min___redArg(
    mut v_inst_113_: *mut crate::leanh::LeanObject,
    mut v_arr_114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: u8 = 0;
    v___x_115_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_116_ = lean_array_fget(v_arr_114_, v___x_115_);
    v___x_117_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_118_ = lean_array_get_size(v_arr_114_);
    v___x_119_ = l_Array_min___redArg___closed__9;
    v___x_120_ = lean_nat_dec_lt(v___x_117_, v___x_118_);
    if v___x_120_ == 0 {
        crate::leanh::lean_dec_ref(v_arr_114_);
        crate::leanh::lean_dec(v_inst_113_);
        return v___x_116_;
    } else {
        let mut v___f_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_122_: u8 = 0;
        v___f_121_ = crate::leanh::lean_alloc_closure(
            l_Array_min___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_121_, 0, v_inst_113_);
        v___x_122_ = lean_nat_dec_le(v___x_118_, v___x_118_);
        if v___x_122_ == 0 {
            if v___x_120_ == 0 {
                crate::leanh::lean_dec_ref(v___f_121_);
                crate::leanh::lean_dec_ref(v_arr_114_);
                return v___x_116_;
            } else {
                let mut v___x_123_: usize = 0;
                let mut v___x_124_: usize = 0;
                let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_123_ = 1usize;
                v___x_124_ = lean_usize_of_nat(v___x_118_);
                v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_119_,
                    v___f_121_,
                    v_arr_114_,
                    v___x_123_,
                    v___x_124_,
                    v___x_116_,
                );
                return v___x_125_;
            }
        } else {
            let mut v___x_126_: usize = 0;
            let mut v___x_127_: usize = 0;
            let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_126_ = 1usize;
            v___x_127_ = lean_usize_of_nat(v___x_118_);
            v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_119_,
                v___f_121_,
                v_arr_114_,
                v___x_126_,
                v___x_127_,
                v___x_116_,
            );
            return v___x_128_;
        }
    }
}
pub unsafe fn l_Array_min(
    mut v_00_u03b1_129_: *mut crate::leanh::LeanObject,
    mut v_inst_130_: *mut crate::leanh::LeanObject,
    mut v_arr_131_: *mut crate::leanh::LeanObject,
    mut v_h_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_133_ = l_Array_min___redArg(v_inst_130_, v_arr_131_);
    return v___x_133_;
}
pub unsafe fn l_Array_min_x3f___redArg(
    mut v_inst_134_: *mut crate::leanh::LeanObject,
    mut v_arr_135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: u8 = 0;
    v___x_136_ = lean_array_get_size(v_arr_135_);
    v___x_137_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
    if v___x_138_ == 0 {
        let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_139_ = l_Array_min___redArg(v_inst_134_, v_arr_135_);
        v___x_140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_140_, 0, v___x_139_);
        return v___x_140_;
    } else {
        let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_arr_135_);
        crate::leanh::lean_dec(v_inst_134_);
        v___x_141_ = crate::leanh::lean_box(0);
        return v___x_141_;
    }
}
pub unsafe fn l_Array_min_x3f(
    mut v_00_u03b1_142_: *mut crate::leanh::LeanObject,
    mut v_inst_143_: *mut crate::leanh::LeanObject,
    mut v_arr_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_145_ = l_Array_min_x3f___redArg(v_inst_143_, v_arr_144_);
    return v___x_145_;
}
pub unsafe fn l_Array_max___redArg(
    mut v_inst_146_: *mut crate::leanh::LeanObject,
    mut v_arr_147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: u8 = 0;
    v___x_148_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_149_ = lean_array_fget(v_arr_147_, v___x_148_);
    v___x_150_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_151_ = lean_array_get_size(v_arr_147_);
    v___x_152_ = l_Array_min___redArg___closed__9;
    v___x_153_ = lean_nat_dec_lt(v___x_150_, v___x_151_);
    if v___x_153_ == 0 {
        crate::leanh::lean_dec_ref(v_arr_147_);
        crate::leanh::lean_dec(v_inst_146_);
        return v___x_149_;
    } else {
        let mut v___f_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: u8 = 0;
        v___f_154_ = crate::leanh::lean_alloc_closure(
            l_Array_min___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_154_, 0, v_inst_146_);
        v___x_155_ = lean_nat_dec_le(v___x_151_, v___x_151_);
        if v___x_155_ == 0 {
            if v___x_153_ == 0 {
                crate::leanh::lean_dec_ref(v___f_154_);
                crate::leanh::lean_dec_ref(v_arr_147_);
                return v___x_149_;
            } else {
                let mut v___x_156_: usize = 0;
                let mut v___x_157_: usize = 0;
                let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_156_ = 1usize;
                v___x_157_ = lean_usize_of_nat(v___x_151_);
                v___x_158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_152_,
                    v___f_154_,
                    v_arr_147_,
                    v___x_156_,
                    v___x_157_,
                    v___x_149_,
                );
                return v___x_158_;
            }
        } else {
            let mut v___x_159_: usize = 0;
            let mut v___x_160_: usize = 0;
            let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_159_ = 1usize;
            v___x_160_ = lean_usize_of_nat(v___x_151_);
            v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_152_,
                v___f_154_,
                v_arr_147_,
                v___x_159_,
                v___x_160_,
                v___x_149_,
            );
            return v___x_161_;
        }
    }
}
pub unsafe fn l_Array_max(
    mut v_00_u03b1_162_: *mut crate::leanh::LeanObject,
    mut v_inst_163_: *mut crate::leanh::LeanObject,
    mut v_arr_164_: *mut crate::leanh::LeanObject,
    mut v_h_165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = l_Array_max___redArg(v_inst_163_, v_arr_164_);
    return v___x_166_;
}
pub unsafe fn l_Array_max_x3f___redArg(
    mut v_inst_167_: *mut crate::leanh::LeanObject,
    mut v_arr_168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: u8 = 0;
    v___x_169_ = lean_array_get_size(v_arr_168_);
    v___x_170_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_171_ = lean_nat_dec_eq(v___x_169_, v___x_170_);
    if v___x_171_ == 0 {
        let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_172_ = l_Array_max___redArg(v_inst_167_, v_arr_168_);
        v___x_173_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_173_, 0, v___x_172_);
        return v___x_173_;
    } else {
        let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_arr_168_);
        crate::leanh::lean_dec(v_inst_167_);
        v___x_174_ = crate::leanh::lean_box(0);
        return v___x_174_;
    }
}
pub unsafe fn l_Array_max_x3f(
    mut v_00_u03b1_175_: *mut crate::leanh::LeanObject,
    mut v_inst_176_: *mut crate::leanh::LeanObject,
    mut v_arr_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_178_ = l_Array_max_x3f___redArg(v_inst_176_, v_arr_177_);
    return v___x_178_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_MinMax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_MinMax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_MinMax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_DecidableEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_MinMax(builtin);
}
