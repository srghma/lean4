// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Fin
// Imports: Init.Data.Range.Polymorphic.Instances Init.Data.Fin.OverflowAware Init.Grind Init.Data.Fin.Lemmas Init.Data.Int.OfNat Init.Data.Nat.Linear Init.Data.Option.Lemmas
use crate::ffi::{lean_nat_add, lean_nat_dec_lt, lean_nat_mod, lean_nat_sub};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Fin::OverflowAware::{
    initialize_Init_Data_Fin_OverflowAware, runtime_initialize_Init_Data_Fin_OverflowAware,
};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Instances::{
    initialize_Init_Data_Range_Polymorphic_Instances,
    runtime_initialize_Init_Data_Range_Polymorphic_Instances,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
pub static mut l_Fin_instLeast_x3fOfNatNat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Fin_instHasSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Fin_instHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Fin_instHasSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Fin_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Fin_instHasSize__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Fin_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Fin_instHasSize__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Fin_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Fin_instUpwardEnumerable___lam__0(
    mut v_n_74_: *mut crate::leanh::LeanObject,
    mut v_i_75_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: u8 = 0;
    v___x_76_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_77_ = lean_nat_add(v_i_75_, v___x_76_);
    v___x_78_ = lean_nat_dec_lt(v___x_77_, v_n_74_);
    if v___x_78_ == 0 {
        let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_77_);
        v___x_79_ = crate::leanh::lean_box(0);
        return v___x_79_;
    } else {
        let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_80_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_80_, 0, v___x_77_);
        return v___x_80_;
    }
}
pub unsafe fn l_Fin_instUpwardEnumerable___lam__0___boxed(
    mut v_n_81_: *mut crate::leanh::LeanObject,
    mut v_i_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Fin_instUpwardEnumerable___lam__0(v_n_81_, v_i_82_);
    crate::leanh::lean_dec(v_i_82_);
    crate::leanh::lean_dec(v_n_81_);
    return v_res_83_;
}
pub unsafe fn l_Fin_instUpwardEnumerable___lam__1(
    mut v_n_84_: *mut crate::leanh::LeanObject,
    mut v_m_85_: *mut crate::leanh::LeanObject,
    mut v_i_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_88_: u8 = 0;
    v___x_87_ = lean_nat_add(v_i_86_, v_m_85_);
    v___x_88_ = lean_nat_dec_lt(v___x_87_, v_n_84_);
    if v___x_88_ == 0 {
        let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_87_);
        v___x_89_ = crate::leanh::lean_box(0);
        return v___x_89_;
    } else {
        let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_90_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_90_, 0, v___x_87_);
        return v___x_90_;
    }
}
pub unsafe fn l_Fin_instUpwardEnumerable___lam__1___boxed(
    mut v_n_91_: *mut crate::leanh::LeanObject,
    mut v_m_92_: *mut crate::leanh::LeanObject,
    mut v_i_93_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_94_ = l_Fin_instUpwardEnumerable___lam__1(v_n_91_, v_m_92_, v_i_93_);
    crate::leanh::lean_dec(v_i_93_);
    crate::leanh::lean_dec(v_m_92_);
    crate::leanh::lean_dec(v_n_91_);
    return v_res_94_;
}
pub unsafe fn l_Fin_instUpwardEnumerable(
    mut v_n_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_95_);
    v___f_96_ = crate::leanh::lean_alloc_closure(
        l_Fin_instUpwardEnumerable___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_96_, 0, v_n_95_);
    v___f_97_ = crate::leanh::lean_alloc_closure(
        l_Fin_instUpwardEnumerable___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_97_, 0, v_n_95_);
    v___x_98_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_98_, 0, v___f_96_);
    crate::leanh::lean_ctor_set(v___x_98_, 1, v___f_97_);
    return v___x_98_;
}
pub unsafe fn _init_l_Fin_instLeast_x3fOfNatNat() -> *mut crate::leanh::LeanObject {
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_99_ = crate::leanh::lean_box(0);
    return v___x_99_;
}
pub unsafe fn l_Fin_instLeast_x3fOfNeZeroNat___redArg(
    mut v_n_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_101_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_102_ = lean_nat_mod(v___x_101_, v_n_100_);
    v___x_103_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_103_, 0, v___x_102_);
    return v___x_103_;
}
pub unsafe fn l_Fin_instLeast_x3fOfNeZeroNat___redArg___boxed(
    mut v_n_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_105_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg(v_n_104_);
    crate::leanh::lean_dec(v_n_104_);
    return v_res_105_;
}
pub unsafe fn l_Fin_instLeast_x3fOfNeZeroNat(
    mut v_n_106_: *mut crate::leanh::LeanObject,
    mut v_inst_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_108_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg(v_n_106_);
    return v___x_108_;
}
pub unsafe fn l_Fin_instLeast_x3fOfNeZeroNat___boxed(
    mut v_n_109_: *mut crate::leanh::LeanObject,
    mut v_inst_110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_111_ = l_Fin_instLeast_x3fOfNeZeroNat(v_n_109_, v_inst_110_);
    crate::leanh::lean_dec(v_n_109_);
    return v_res_111_;
}
pub unsafe fn l_Fin_instHasSize___lam__0(
    mut v_lo_112_: *mut crate::leanh::LeanObject,
    mut v_hi_113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_114_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_115_ = lean_nat_add(v_hi_113_, v___x_114_);
    v___x_116_ = lean_nat_sub(v___x_115_, v_lo_112_);
    crate::leanh::lean_dec(v___x_115_);
    return v___x_116_;
}
pub unsafe fn l_Fin_instHasSize___lam__0___boxed(
    mut v_lo_117_: *mut crate::leanh::LeanObject,
    mut v_hi_118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_119_ = l_Fin_instHasSize___lam__0(v_lo_117_, v_hi_118_);
    crate::leanh::lean_dec(v_hi_118_);
    crate::leanh::lean_dec(v_lo_117_);
    return v_res_119_;
}
pub unsafe fn l_Fin_instHasSize(
    mut v_n_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_122_ = l_Fin_instHasSize___closed__0;
    return v___f_122_;
}
pub unsafe fn l_Fin_instHasSize___boxed(
    mut v_n_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_124_ = l_Fin_instHasSize(v_n_123_);
    crate::leanh::lean_dec(v_n_123_);
    return v_res_124_;
}
pub unsafe fn l_Fin_instHasSize__1___lam__0(
    mut v_lo_125_: *mut crate::leanh::LeanObject,
    mut v_hi_126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_127_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_128_ = lean_nat_add(v_hi_126_, v___x_127_);
    v___x_129_ = lean_nat_sub(v___x_128_, v_lo_125_);
    crate::leanh::lean_dec(v___x_128_);
    v___x_130_ = lean_nat_sub(v___x_129_, v___x_127_);
    crate::leanh::lean_dec(v___x_129_);
    return v___x_130_;
}
pub unsafe fn l_Fin_instHasSize__1___lam__0___boxed(
    mut v_lo_131_: *mut crate::leanh::LeanObject,
    mut v_hi_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_133_ = l_Fin_instHasSize__1___lam__0(v_lo_131_, v_hi_132_);
    crate::leanh::lean_dec(v_hi_132_);
    crate::leanh::lean_dec(v_lo_131_);
    return v_res_133_;
}
pub unsafe fn l_Fin_instHasSize__1(
    mut v_n_135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_136_ = l_Fin_instHasSize__1___closed__0;
    return v___f_136_;
}
pub unsafe fn l_Fin_instHasSize__1___boxed(
    mut v_n_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_138_ = l_Fin_instHasSize__1(v_n_137_);
    crate::leanh::lean_dec(v_n_137_);
    return v_res_138_;
}
pub unsafe fn l_Fin_instHasSize__2___lam__0(
    mut v_n_139_: *mut crate::leanh::LeanObject,
    mut v_lo_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_141_ = lean_nat_sub(v_n_139_, v_lo_140_);
    return v___x_141_;
}
pub unsafe fn l_Fin_instHasSize__2___lam__0___boxed(
    mut v_n_142_: *mut crate::leanh::LeanObject,
    mut v_lo_143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_144_ = l_Fin_instHasSize__2___lam__0(v_n_142_, v_lo_143_);
    crate::leanh::lean_dec(v_lo_143_);
    crate::leanh::lean_dec(v_n_142_);
    return v_res_144_;
}
pub unsafe fn l_Fin_instHasSize__2(
    mut v_n_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_146_ = crate::leanh::lean_alloc_closure(
        l_Fin_instHasSize__2___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_146_, 0, v_n_145_);
    return v___f_146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Fin(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_OverflowAware(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Fin_instLeast_x3fOfNatNat = _init_l_Fin_instLeast_x3fOfNatNat();
    crate::leanh::lean_mark_persistent(l_Fin_instLeast_x3fOfNatNat);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Fin(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Fin(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_OverflowAware(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Fin(builtin);
}
