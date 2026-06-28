// Lean compiler output
// Module: Init.Data.Range.Polymorphic.BitVec
// Imports: Init.Data.Range.Polymorphic.Instances Init.Omega Init.Data.BitVec.Bootstrap Init.Data.BitVec.Lemmas Init.Data.Nat.Lemmas Init.Data.Option.Lemmas
use crate::r#gen::Init::Data::BitVec::BasicAux::l_BitVec_add;
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Instances::{
    initialize_Init_Data_Range_Polymorphic_Instances,
    runtime_initialize_Init_Data_Range_Polymorphic_Instances,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_pow, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub static l_BitVec_instRxcHasSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_BitVec_instRxcHasSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_BitVec_instRxcHasSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_BitVec_instRxcHasSize___closed__0_value) as *mut LeanObject;
pub static l_BitVec_instRxoHasSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_BitVec_instRxoHasSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_BitVec_instRxoHasSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_BitVec_instRxoHasSize___closed__0_value) as *mut LeanObject;
pub unsafe fn l_BitVec_instUpwardEnumerable___lam__0(
    mut v_n_68_: *mut LeanObject,
    mut v_i_69_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_75_: u8 = 0;
    v___x_70_ = lean_unsigned_to_nat(1);
    v___x_71_ = l_BitVec_ofNat(v_n_68_, v___x_70_);
    v___x_72_ = l_BitVec_add(v_n_68_, v_i_69_, v___x_71_);
    lean_dec(v___x_71_);
    v___x_73_ = lean_unsigned_to_nat(0);
    v___x_74_ = l_BitVec_ofNat(v_n_68_, v___x_73_);
    v___x_75_ = lean_nat_dec_eq(v___x_72_, v___x_74_);
    lean_dec(v___x_74_);
    if v___x_75_ == 0 {
        let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
        v___x_76_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_76_, 0, v___x_72_);
        return v___x_76_;
    } else {
        let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_72_);
        v___x_77_ = lean_box(0);
        return v___x_77_;
    }
}
pub unsafe fn l_BitVec_instUpwardEnumerable___lam__0___boxed(
    mut v_n_78_: *mut LeanObject,
    mut v_i_79_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_80_: *mut LeanObject = core::ptr::null_mut();
    v_res_80_ = l_BitVec_instUpwardEnumerable___lam__0(v_n_78_, v_i_79_);
    lean_dec(v_i_79_);
    lean_dec(v_n_78_);
    return v_res_80_;
}
pub unsafe fn l_BitVec_instUpwardEnumerable___lam__1(
    mut v_n_81_: *mut LeanObject,
    mut v_m_82_: *mut LeanObject,
    mut v_i_83_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_87_: u8 = 0;
    v___x_84_ = lean_nat_add(v_i_83_, v_m_82_);
    v___x_85_ = lean_unsigned_to_nat(2);
    v___x_86_ = lean_nat_pow(v___x_85_, v_n_81_);
    v___x_87_ = lean_nat_dec_lt(v___x_84_, v___x_86_);
    lean_dec(v___x_86_);
    if v___x_87_ == 0 {
        let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_84_);
        v___x_88_ = lean_box(0);
        return v___x_88_;
    } else {
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        v___x_89_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_89_, 0, v___x_84_);
        return v___x_89_;
    }
}
pub unsafe fn l_BitVec_instUpwardEnumerable___lam__1___boxed(
    mut v_n_90_: *mut LeanObject,
    mut v_m_91_: *mut LeanObject,
    mut v_i_92_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_93_: *mut LeanObject = core::ptr::null_mut();
    v_res_93_ = l_BitVec_instUpwardEnumerable___lam__1(v_n_90_, v_m_91_, v_i_92_);
    lean_dec(v_i_92_);
    lean_dec(v_m_91_);
    lean_dec(v_n_90_);
    return v_res_93_;
}
pub unsafe fn l_BitVec_instUpwardEnumerable(mut v_n_94_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_95_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_94_);
    v___f_95_ = lean_alloc_closure(
        l_BitVec_instUpwardEnumerable___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_95_, 0, v_n_94_);
    v___f_96_ = lean_alloc_closure(
        l_BitVec_instUpwardEnumerable___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_96_, 0, v_n_94_);
    v___x_97_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_97_, 0, v___f_95_);
    lean_ctor_set(v___x_97_, 1, v___f_96_);
    return v___x_97_;
}
pub unsafe fn l_BitVec_instRxcHasSize___lam__0(
    mut v_lo_98_: *mut LeanObject,
    mut v_hi_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    v___x_100_ = lean_unsigned_to_nat(1);
    v___x_101_ = lean_nat_add(v_hi_99_, v___x_100_);
    v___x_102_ = lean_nat_sub(v___x_101_, v_lo_98_);
    lean_dec(v___x_101_);
    return v___x_102_;
}
pub unsafe fn l_BitVec_instRxcHasSize___lam__0___boxed(
    mut v_lo_103_: *mut LeanObject,
    mut v_hi_104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_105_: *mut LeanObject = core::ptr::null_mut();
    v_res_105_ = l_BitVec_instRxcHasSize___lam__0(v_lo_103_, v_hi_104_);
    lean_dec(v_hi_104_);
    lean_dec(v_lo_103_);
    return v_res_105_;
}
pub unsafe fn l_BitVec_instRxcHasSize(mut v_n_107_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_108_: *mut LeanObject = core::ptr::null_mut();
    v___f_108_ = l_BitVec_instRxcHasSize___closed__0;
    return v___f_108_;
}
pub unsafe fn l_BitVec_instRxcHasSize___boxed(mut v_n_109_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_110_: *mut LeanObject = core::ptr::null_mut();
    v_res_110_ = l_BitVec_instRxcHasSize(v_n_109_);
    lean_dec(v_n_109_);
    return v_res_110_;
}
pub unsafe fn l_BitVec_instRxoHasSize___lam__0(
    mut v_lo_111_: *mut LeanObject,
    mut v_hi_112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    v___x_113_ = lean_unsigned_to_nat(1);
    v___x_114_ = lean_nat_add(v_hi_112_, v___x_113_);
    v___x_115_ = lean_nat_sub(v___x_114_, v_lo_111_);
    lean_dec(v___x_114_);
    v___x_116_ = lean_nat_sub(v___x_115_, v___x_113_);
    lean_dec(v___x_115_);
    return v___x_116_;
}
pub unsafe fn l_BitVec_instRxoHasSize___lam__0___boxed(
    mut v_lo_117_: *mut LeanObject,
    mut v_hi_118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_119_: *mut LeanObject = core::ptr::null_mut();
    v_res_119_ = l_BitVec_instRxoHasSize___lam__0(v_lo_117_, v_hi_118_);
    lean_dec(v_hi_118_);
    lean_dec(v_lo_117_);
    return v_res_119_;
}
pub unsafe fn l_BitVec_instRxoHasSize(mut v_n_121_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_122_: *mut LeanObject = core::ptr::null_mut();
    v___f_122_ = l_BitVec_instRxoHasSize___closed__0;
    return v___f_122_;
}
pub unsafe fn l_BitVec_instRxoHasSize___boxed(mut v_n_123_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_124_: *mut LeanObject = core::ptr::null_mut();
    v_res_124_ = l_BitVec_instRxoHasSize(v_n_123_);
    lean_dec(v_n_123_);
    return v_res_124_;
}
pub unsafe fn l_BitVec_instRxiHasSize___lam__0(
    mut v_n_125_: *mut LeanObject,
    mut v_lo_126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    v___x_127_ = lean_unsigned_to_nat(2);
    v___x_128_ = lean_nat_pow(v___x_127_, v_n_125_);
    v___x_129_ = lean_nat_sub(v___x_128_, v_lo_126_);
    lean_dec(v___x_128_);
    return v___x_129_;
}
pub unsafe fn l_BitVec_instRxiHasSize___lam__0___boxed(
    mut v_n_130_: *mut LeanObject,
    mut v_lo_131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_132_: *mut LeanObject = core::ptr::null_mut();
    v_res_132_ = l_BitVec_instRxiHasSize___lam__0(v_n_130_, v_lo_131_);
    lean_dec(v_lo_131_);
    lean_dec(v_n_130_);
    return v_res_132_;
}
pub unsafe fn l_BitVec_instRxiHasSize(mut v_n_133_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_134_: *mut LeanObject = core::ptr::null_mut();
    v___f_134_ = lean_alloc_closure(
        l_BitVec_instRxiHasSize___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_134_, 0, v_n_133_);
    return v___f_134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_BitVec(
    builtin: u8,
) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_BitVec(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_BitVec(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
}
