// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Fin
// Imports: Init.Data.Range.Polymorphic.Instances Init.Data.Fin.OverflowAware Init.Grind Init.Data.Fin.Lemmas Init.Data.Int.OfNat Init.Data.Nat.Linear Init.Data.Option.Lemmas
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_lt, lean_nat_mod, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_unsigned_to_nat,
};
pub static mut l_Fin_instLeast_x3fOfNatNat: *mut LeanObject = core::ptr::null_mut();
pub static l_Fin_instHasSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Fin_instHasSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Fin_instHasSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Fin_instHasSize___closed__0_value) as *mut LeanObject;
pub static l_Fin_instHasSize__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Fin_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Fin_instHasSize__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Fin_instHasSize__1___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Fin_instUpwardEnumerable___lam__0(
    mut v_n_74_: *mut LeanObject,
    mut v_i_75_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_78_: u8 = 0;
    v___x_76_ = lean_unsigned_to_nat(1);
    v___x_77_ = lean_nat_add(v_i_75_, v___x_76_);
    v___x_78_ = lean_nat_dec_lt(v___x_77_, v_n_74_);
    if v___x_78_ == 0 {
        let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_77_);
        v___x_79_ = lean_box(0);
        return v___x_79_;
    } else {
        let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
        v___x_80_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_80_, 0, v___x_77_);
        return v___x_80_;
    }
}
pub unsafe fn l_Fin_instUpwardEnumerable___lam__0___boxed(
    mut v_n_81_: *mut LeanObject,
    mut v_i_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_83_: *mut LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Fin_instUpwardEnumerable___lam__0(v_n_81_, v_i_82_);
    lean_dec(v_i_82_);
    lean_dec(v_n_81_);
    return v_res_83_;
}
pub unsafe fn l_Fin_instUpwardEnumerable___lam__1(
    mut v_n_84_: *mut LeanObject,
    mut v_m_85_: *mut LeanObject,
    mut v_i_86_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_88_: u8 = 0;
    v___x_87_ = lean_nat_add(v_i_86_, v_m_85_);
    v___x_88_ = lean_nat_dec_lt(v___x_87_, v_n_84_);
    if v___x_88_ == 0 {
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_87_);
        v___x_89_ = lean_box(0);
        return v___x_89_;
    } else {
        let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
        v___x_90_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_90_, 0, v___x_87_);
        return v___x_90_;
    }
}
pub unsafe fn l_Fin_instUpwardEnumerable___lam__1___boxed(
    mut v_n_91_: *mut LeanObject,
    mut v_m_92_: *mut LeanObject,
    mut v_i_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_94_: *mut LeanObject = core::ptr::null_mut();
    v_res_94_ = l_Fin_instUpwardEnumerable___lam__1(v_n_91_, v_m_92_, v_i_93_);
    lean_dec(v_i_93_);
    lean_dec(v_m_92_);
    lean_dec(v_n_91_);
    return v_res_94_;
}
pub unsafe fn l_Fin_instUpwardEnumerable(mut v_n_95_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_95_);
    v___f_96_ = lean_alloc_closure(
        l_Fin_instUpwardEnumerable___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_96_, 0, v_n_95_);
    v___f_97_ = lean_alloc_closure(
        l_Fin_instUpwardEnumerable___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_97_, 0, v_n_95_);
    v___x_98_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_98_, 0, v___f_96_);
    lean_ctor_set(v___x_98_, 1, v___f_97_);
    return v___x_98_;
}
pub unsafe fn _init_l_Fin_instLeast_x3fOfNatNat() -> *mut LeanObject {
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    v___x_99_ = lean_box(0);
    return v___x_99_;
}
pub unsafe fn l_Fin_instLeast_x3fOfNeZeroNat___redArg(
    mut v_n_100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    v___x_101_ = lean_unsigned_to_nat(0);
    v___x_102_ = lean_nat_mod(v___x_101_, v_n_100_);
    v___x_103_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_103_, 0, v___x_102_);
    return v___x_103_;
}
pub unsafe fn l_Fin_instLeast_x3fOfNeZeroNat___redArg___boxed(
    mut v_n_104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_105_: *mut LeanObject = core::ptr::null_mut();
    v_res_105_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg(v_n_104_);
    lean_dec(v_n_104_);
    return v_res_105_;
}
pub unsafe fn l_Fin_instLeast_x3fOfNeZeroNat(
    mut v_n_106_: *mut LeanObject,
    mut v_inst_107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    v___x_108_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg(v_n_106_);
    return v___x_108_;
}
pub unsafe fn l_Fin_instLeast_x3fOfNeZeroNat___boxed(
    mut v_n_109_: *mut LeanObject,
    mut v_inst_110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_111_: *mut LeanObject = core::ptr::null_mut();
    v_res_111_ = l_Fin_instLeast_x3fOfNeZeroNat(v_n_109_, v_inst_110_);
    lean_dec(v_n_109_);
    return v_res_111_;
}
pub unsafe fn l_Fin_instHasSize___lam__0(
    mut v_lo_112_: *mut LeanObject,
    mut v_hi_113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    v___x_114_ = lean_unsigned_to_nat(1);
    v___x_115_ = lean_nat_add(v_hi_113_, v___x_114_);
    v___x_116_ = lean_nat_sub(v___x_115_, v_lo_112_);
    lean_dec(v___x_115_);
    return v___x_116_;
}
pub unsafe fn l_Fin_instHasSize___lam__0___boxed(
    mut v_lo_117_: *mut LeanObject,
    mut v_hi_118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_119_: *mut LeanObject = core::ptr::null_mut();
    v_res_119_ = l_Fin_instHasSize___lam__0(v_lo_117_, v_hi_118_);
    lean_dec(v_hi_118_);
    lean_dec(v_lo_117_);
    return v_res_119_;
}
pub unsafe fn l_Fin_instHasSize(mut v_n_121_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_122_: *mut LeanObject = core::ptr::null_mut();
    v___f_122_ = l_Fin_instHasSize___closed__0;
    return v___f_122_;
}
pub unsafe fn l_Fin_instHasSize___boxed(mut v_n_123_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_124_: *mut LeanObject = core::ptr::null_mut();
    v_res_124_ = l_Fin_instHasSize(v_n_123_);
    lean_dec(v_n_123_);
    return v_res_124_;
}
pub unsafe fn l_Fin_instHasSize__1___lam__0(
    mut v_lo_125_: *mut LeanObject,
    mut v_hi_126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    v___x_127_ = lean_unsigned_to_nat(1);
    v___x_128_ = lean_nat_add(v_hi_126_, v___x_127_);
    v___x_129_ = lean_nat_sub(v___x_128_, v_lo_125_);
    lean_dec(v___x_128_);
    v___x_130_ = lean_nat_sub(v___x_129_, v___x_127_);
    lean_dec(v___x_129_);
    return v___x_130_;
}
pub unsafe fn l_Fin_instHasSize__1___lam__0___boxed(
    mut v_lo_131_: *mut LeanObject,
    mut v_hi_132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_133_: *mut LeanObject = core::ptr::null_mut();
    v_res_133_ = l_Fin_instHasSize__1___lam__0(v_lo_131_, v_hi_132_);
    lean_dec(v_hi_132_);
    lean_dec(v_lo_131_);
    return v_res_133_;
}
pub unsafe fn l_Fin_instHasSize__1(mut v_n_135_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_136_: *mut LeanObject = core::ptr::null_mut();
    v___f_136_ = l_Fin_instHasSize__1___closed__0;
    return v___f_136_;
}
pub unsafe fn l_Fin_instHasSize__1___boxed(mut v_n_137_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_138_: *mut LeanObject = core::ptr::null_mut();
    v_res_138_ = l_Fin_instHasSize__1(v_n_137_);
    lean_dec(v_n_137_);
    return v_res_138_;
}
pub unsafe fn l_Fin_instHasSize__2___lam__0(
    mut v_n_139_: *mut LeanObject,
    mut v_lo_140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
    v___x_141_ = lean_nat_sub(v_n_139_, v_lo_140_);
    return v___x_141_;
}
pub unsafe fn l_Fin_instHasSize__2___lam__0___boxed(
    mut v_n_142_: *mut LeanObject,
    mut v_lo_143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_144_: *mut LeanObject = core::ptr::null_mut();
    v_res_144_ = l_Fin_instHasSize__2___lam__0(v_n_142_, v_lo_143_);
    lean_dec(v_lo_143_);
    lean_dec(v_n_142_);
    return v_res_144_;
}
pub unsafe fn l_Fin_instHasSize__2(mut v_n_145_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_146_: *mut LeanObject = core::ptr::null_mut();
    v___f_146_ = lean_alloc_closure(
        l_Fin_instHasSize__2___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_146_, 0, v_n_145_);
    return v___f_146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Fin(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_OverflowAware(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Fin_instLeast_x3fOfNatNat = _init_l_Fin_instLeast_x3fOfNatNat();
    lean_mark_persistent(l_Fin_instLeast_x3fOfNatNat);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Fin(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Fin(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Fin_OverflowAware(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Fin(builtin);
}
