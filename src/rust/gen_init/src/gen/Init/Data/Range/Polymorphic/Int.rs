// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Int
// Imports: Init.Data.Range.Polymorphic.Instances Init.Omega
use crate::ffi::{lean_int_add, lean_int_sub, lean_nat_sub, lean_nat_to_int};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Range::Polymorphic::Instances::{
    initialize_Init_Data_Range_Polymorphic_Instances,
    runtime_initialize_Init_Data_Range_Polymorphic_Instances,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
static mut l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_PRange_instUpwardEnumerableInt___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_PRange_instUpwardEnumerableInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instUpwardEnumerableInt___closed__1_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_PRange_instUpwardEnumerableInt___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instUpwardEnumerableInt___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_PRange_instUpwardEnumerableInt___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_PRange_instUpwardEnumerableInt: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableInt___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instHasSizeInt___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_PRange_instHasSizeInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_PRange_instHasSizeInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_PRange_instHasSizeInt: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instHasSizeInt__1___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_PRange_instHasSizeInt__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_PRange_instHasSizeInt__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeInt__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_PRange_instHasSizeInt__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeInt__1___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_47_ = leanh::lean_unsigned_to_nat(1);
    v___x_48_ = lean_nat_to_int(v___x_47_);
    return v___x_48_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableInt___lam__0(
    mut v_x_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_51_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_50_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once),
        _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0,
    );
    v___x_51_ = lean_int_add(v_x_49_, v___x_50_);
    v___x_52_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_52_, 0, v___x_51_);
    return v___x_52_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed(
    mut v_x_53_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_54_ = l_Std_PRange_instUpwardEnumerableInt___lam__0(v_x_53_);
    leanh::lean_dec(v_x_53_);
    return v_res_54_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableInt___lam__1(
    mut v_n_55_: *mut leanh::LeanObject,
    mut v_x_56_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_57_ = lean_nat_to_int(v_n_55_);
    v___x_58_ = lean_int_add(v_x_56_, v___x_57_);
    leanh::lean_dec(v___x_57_);
    v___x_59_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_59_, 0, v___x_58_);
    return v___x_59_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed(
    mut v_n_60_: *mut leanh::LeanObject,
    mut v_x_61_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Std_PRange_instUpwardEnumerableInt___lam__1(v_n_60_, v_x_61_);
    leanh::lean_dec(v_x_61_);
    return v_res_62_;
}
pub unsafe fn l_Std_PRange_instHasSizeInt___lam__0(
    mut v_lo_69_: *mut leanh::LeanObject,
    mut v_hi_70_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_71_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once),
        _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0,
    );
    v___x_72_ = lean_int_add(v_hi_70_, v___x_71_);
    v___x_73_ = lean_int_sub(v___x_72_, v_lo_69_);
    leanh::lean_dec(v___x_72_);
    v___x_74_ = l_Int_toNat(v___x_73_);
    leanh::lean_dec(v___x_73_);
    return v___x_74_;
}
pub unsafe fn l_Std_PRange_instHasSizeInt___lam__0___boxed(
    mut v_lo_75_: *mut leanh::LeanObject,
    mut v_hi_76_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_77_ = l_Std_PRange_instHasSizeInt___lam__0(v_lo_75_, v_hi_76_);
    leanh::lean_dec(v_hi_76_);
    leanh::lean_dec(v_lo_75_);
    return v_res_77_;
}
pub unsafe fn l_Std_PRange_instHasSizeInt__1___lam__0(
    mut v_lo_80_: *mut leanh::LeanObject,
    mut v_hi_81_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_82_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_82_ = leanh::lean_unsigned_to_nat(1);
    v___x_83_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once),
        _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0,
    );
    v___x_84_ = lean_int_add(v_hi_81_, v___x_83_);
    v___x_85_ = lean_int_sub(v___x_84_, v_lo_80_);
    leanh::lean_dec(v___x_84_);
    v___x_86_ = l_Int_toNat(v___x_85_);
    leanh::lean_dec(v___x_85_);
    v___x_87_ = lean_nat_sub(v___x_86_, v___x_82_);
    leanh::lean_dec(v___x_86_);
    return v___x_87_;
}
pub unsafe fn l_Std_PRange_instHasSizeInt__1___lam__0___boxed(
    mut v_lo_88_: *mut leanh::LeanObject,
    mut v_hi_89_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_90_ = l_Std_PRange_instHasSizeInt__1___lam__0(v_lo_88_, v_hi_89_);
    leanh::lean_dec(v_hi_89_);
    leanh::lean_dec(v_lo_88_);
    return v_res_90_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Int(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Int(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Int(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Int(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Int(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Int(builtin);
}