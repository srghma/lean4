// Lean compiler output
// Module: Init.Data.Int.Bitwise.Basic
// Imports: Init.Data.Int.Basic Init.Data.Nat.Bitwise.Basic
use crate::r#gen::Init::Data::Int::Basic::{
    initialize_Init_Data_Int_Basic, runtime_initialize_Init_Data_Int_Basic,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_int_neg_succ_of_nat, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_shiftl, lean_nat_shiftr};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Int_not___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_not___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Int_instComplement___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_not___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int_instComplement___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instComplement___closed__0_value) as *mut LeanObject;
pub static mut l_Int_instComplement: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instComplement___closed__0_value) as *mut LeanObject;
pub static l_Int_instHShiftRightNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_shiftRight___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int_instHShiftRightNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instHShiftRightNat___closed__0_value) as *mut LeanObject;
pub static mut l_Int_instHShiftRightNat: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instHShiftRightNat___closed__0_value) as *mut LeanObject;
pub static l_Int_instHShiftLeftNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_shiftLeft___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int_instHShiftLeftNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instHShiftLeftNat___closed__0_value) as *mut LeanObject;
pub static mut l_Int_instHShiftLeftNat: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instHShiftLeftNat___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Int_not___closed__0() -> *mut LeanObject {
    let mut v_natZero_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_53_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_52_ = lean_unsigned_to_nat(0);
    v_intZero_53_ = lean_nat_to_int(v_natZero_52_);
    return v_intZero_53_;
}
pub unsafe fn l_Int_not(mut v_x_54_: *mut LeanObject) -> *mut LeanObject {
    let mut v_intZero_55_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_56_: u8 = 0;
    v_intZero_55_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_not___closed__0),
        core::ptr::addr_of_mut!(l_Int_not___closed__0_once),
        _init_l_Int_not___closed__0,
    );
    v_isNeg_56_ = lean_int_dec_lt(v_x_54_, v_intZero_55_);
    if v_isNeg_56_ == 0 {
        let mut v_a_57_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
        v_a_57_ = lean_nat_abs(v_x_54_);
        v___x_58_ = lean_int_neg_succ_of_nat(v_a_57_);
        return v___x_58_;
    } else {
        let mut v_abs_59_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_60_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_61_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
        v_abs_59_ = lean_nat_abs(v_x_54_);
        v_one_60_ = lean_unsigned_to_nat(1);
        v_a_61_ = lean_nat_sub(v_abs_59_, v_one_60_);
        lean_dec(v_abs_59_);
        v___x_62_ = lean_nat_to_int(v_a_61_);
        return v___x_62_;
    }
}
pub unsafe fn l_Int_not___boxed(mut v_x_63_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_64_: *mut LeanObject = core::ptr::null_mut();
    v_res_64_ = l_Int_not(v_x_63_);
    lean_dec(v_x_63_);
    return v_res_64_;
}
pub unsafe fn l_Int_shiftRight(
    mut v_x_67_: *mut LeanObject,
    mut v_x_68_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_69_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_70_: u8 = 0;
    v_intZero_69_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_not___closed__0),
        core::ptr::addr_of_mut!(l_Int_not___closed__0_once),
        _init_l_Int_not___closed__0,
    );
    v_isNeg_70_ = lean_int_dec_lt(v_x_67_, v_intZero_69_);
    if v_isNeg_70_ == 0 {
        let mut v_a_71_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
        v_a_71_ = lean_nat_abs(v_x_67_);
        v___x_72_ = lean_nat_shiftr(v_a_71_, v_x_68_);
        lean_dec(v_a_71_);
        v___x_73_ = lean_nat_to_int(v___x_72_);
        return v___x_73_;
    } else {
        let mut v_abs_74_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_75_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_76_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
        v_abs_74_ = lean_nat_abs(v_x_67_);
        v_one_75_ = lean_unsigned_to_nat(1);
        v_a_76_ = lean_nat_sub(v_abs_74_, v_one_75_);
        lean_dec(v_abs_74_);
        v___x_77_ = lean_nat_shiftr(v_a_76_, v_x_68_);
        lean_dec(v_a_76_);
        v___x_78_ = lean_int_neg_succ_of_nat(v___x_77_);
        return v___x_78_;
    }
}
pub unsafe fn l_Int_shiftRight___boxed(
    mut v_x_79_: *mut LeanObject,
    mut v_x_80_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_81_: *mut LeanObject = core::ptr::null_mut();
    v_res_81_ = l_Int_shiftRight(v_x_79_, v_x_80_);
    lean_dec(v_x_80_);
    lean_dec(v_x_79_);
    return v_res_81_;
}
pub unsafe fn l_Int_shiftLeft(
    mut v_x_84_: *mut LeanObject,
    mut v_x_85_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_87_: u8 = 0;
    v_intZero_86_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_not___closed__0),
        core::ptr::addr_of_mut!(l_Int_not___closed__0_once),
        _init_l_Int_not___closed__0,
    );
    v_isNeg_87_ = lean_int_dec_lt(v_x_84_, v_intZero_86_);
    if v_isNeg_87_ == 0 {
        let mut v_a_88_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
        v_a_88_ = lean_nat_abs(v_x_84_);
        v___x_89_ = lean_nat_shiftl(v_a_88_, v_x_85_);
        lean_dec(v_a_88_);
        v___x_90_ = lean_nat_to_int(v___x_89_);
        return v___x_90_;
    } else {
        let mut v_abs_91_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_92_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_93_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
        v_abs_91_ = lean_nat_abs(v_x_84_);
        v_one_92_ = lean_unsigned_to_nat(1);
        v_a_93_ = lean_nat_sub(v_abs_91_, v_one_92_);
        lean_dec(v_abs_91_);
        v___x_94_ = lean_nat_add(v_a_93_, v_one_92_);
        lean_dec(v_a_93_);
        v___x_95_ = lean_nat_shiftl(v___x_94_, v_x_85_);
        lean_dec(v___x_94_);
        v___x_96_ = lean_nat_sub(v___x_95_, v_one_92_);
        lean_dec(v___x_95_);
        v___x_97_ = lean_int_neg_succ_of_nat(v___x_96_);
        return v___x_97_;
    }
}
pub unsafe fn l_Int_shiftLeft___boxed(
    mut v_x_98_: *mut LeanObject,
    mut v_x_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_100_: *mut LeanObject = core::ptr::null_mut();
    v_res_100_ = l_Int_shiftLeft(v_x_98_, v_x_99_);
    lean_dec(v_x_99_);
    lean_dec(v_x_98_);
    return v_res_100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_Bitwise_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_Bitwise_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Int_Bitwise_Basic(builtin);
}
