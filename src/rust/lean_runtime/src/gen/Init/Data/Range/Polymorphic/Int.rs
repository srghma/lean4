// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Int
// Imports: Init.Data.Range.Polymorphic.Instances Init.Omega
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Range::Polymorphic::Instances::{
    initialize_Init_Data_Range_Polymorphic_Instances,
    runtime_initialize_Init_Data_Range_Polymorphic_Instances,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::lean_imports_rs::Init::Data::Int::Basic::{lean_int_add, lean_int_sub, lean_nat_to_int};
use crate::lean_imports_rs::Init::Prelude::lean_nat_sub;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
    lean_unsigned_to_nat,
};
static mut l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_PRange_instUpwardEnumerableInt___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_PRange_instUpwardEnumerableInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__0_value) as *mut LeanObject;
pub static l_Std_PRange_instUpwardEnumerableInt___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_PRange_instUpwardEnumerableInt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__1_value) as *mut LeanObject;
pub static l_Std_PRange_instUpwardEnumerableInt___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_PRange_instUpwardEnumerableInt___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__2_value) as *mut LeanObject;
pub static mut l_Std_PRange_instUpwardEnumerableInt: *mut LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__2_value) as *mut LeanObject;
pub static l_Std_PRange_instHasSizeInt___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_PRange_instHasSizeInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_PRange_instHasSizeInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeInt___closed__0_value) as *mut LeanObject;
pub static mut l_Std_PRange_instHasSizeInt: *mut LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeInt___closed__0_value) as *mut LeanObject;
pub static l_Std_PRange_instHasSizeInt__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_PRange_instHasSizeInt__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_PRange_instHasSizeInt__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeInt__1___closed__0_value) as *mut LeanObject;
pub static mut l_Std_PRange_instHasSizeInt__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeInt__1___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
    v___x_47_ = lean_unsigned_to_nat(1);
    v___x_48_ = lean_nat_to_int(v___x_47_);
    return v___x_48_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableInt___lam__0(
    mut v_x_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    v___x_50_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once),
        _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0,
    );
    v___x_51_ = lean_int_add(v_x_49_, v___x_50_);
    v___x_52_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_52_, 0, v___x_51_);
    return v___x_52_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed(
    mut v_x_53_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_54_: *mut LeanObject = core::ptr::null_mut();
    v_res_54_ = l_Std_PRange_instUpwardEnumerableInt___lam__0(v_x_53_);
    lean_dec(v_x_53_);
    return v_res_54_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableInt___lam__1(
    mut v_n_55_: *mut LeanObject,
    mut v_x_56_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut LeanObject = core::ptr::null_mut();
    v___x_57_ = lean_nat_to_int(v_n_55_);
    v___x_58_ = lean_int_add(v_x_56_, v___x_57_);
    lean_dec(v___x_57_);
    v___x_59_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_59_, 0, v___x_58_);
    return v___x_59_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed(
    mut v_n_60_: *mut LeanObject,
    mut v_x_61_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_62_: *mut LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Std_PRange_instUpwardEnumerableInt___lam__1(v_n_60_, v_x_61_);
    lean_dec(v_x_61_);
    return v_res_62_;
}
pub unsafe fn l_Std_PRange_instHasSizeInt___lam__0(
    mut v_lo_69_: *mut LeanObject,
    mut v_hi_70_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
    v___x_71_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once),
        _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0,
    );
    v___x_72_ = lean_int_add(v_hi_70_, v___x_71_);
    v___x_73_ = lean_int_sub(v___x_72_, v_lo_69_);
    lean_dec(v___x_72_);
    v___x_74_ = l_Int_toNat(v___x_73_);
    lean_dec(v___x_73_);
    return v___x_74_;
}
pub unsafe fn l_Std_PRange_instHasSizeInt___lam__0___boxed(
    mut v_lo_75_: *mut LeanObject,
    mut v_hi_76_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_77_: *mut LeanObject = core::ptr::null_mut();
    v_res_77_ = l_Std_PRange_instHasSizeInt___lam__0(v_lo_75_, v_hi_76_);
    lean_dec(v_hi_76_);
    lean_dec(v_lo_75_);
    return v_res_77_;
}
pub unsafe fn l_Std_PRange_instHasSizeInt__1___lam__0(
    mut v_lo_80_: *mut LeanObject,
    mut v_hi_81_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
    v___x_82_ = lean_unsigned_to_nat(1);
    v___x_83_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once),
        _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0,
    );
    v___x_84_ = lean_int_add(v_hi_81_, v___x_83_);
    v___x_85_ = lean_int_sub(v___x_84_, v_lo_80_);
    lean_dec(v___x_84_);
    v___x_86_ = l_Int_toNat(v___x_85_);
    lean_dec(v___x_85_);
    v___x_87_ = lean_nat_sub(v___x_86_, v___x_82_);
    lean_dec(v___x_86_);
    return v___x_87_;
}
pub unsafe fn l_Std_PRange_instHasSizeInt__1___lam__0___boxed(
    mut v_lo_88_: *mut LeanObject,
    mut v_hi_89_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_90_: *mut LeanObject = core::ptr::null_mut();
    v_res_90_ = l_Std_PRange_instHasSizeInt__1___lam__0(v_lo_88_, v_hi_89_);
    lean_dec(v_hi_89_);
    lean_dec(v_lo_88_);
    return v_res_90_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Int(builtin: u8) -> *mut LeanObject {
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
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Int(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Int(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Data_Range_Polymorphic_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Int(builtin);
}
