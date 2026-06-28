// Lean compiler output
// Module: Init.Data.Range.Polymorphic.UpwardEnumerable
// Imports: Init.Data.Order.Classes Init.Classical Init.Data.Option.Lemmas
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_PRange_UpwardEnumerable_succ___redArg(
    mut v_inst_68_: *mut LeanObject,
    mut v_a_69_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_72_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_70_ = lean_ctor_get(v_inst_68_, 0);
    lean_inc_ref(v_succ_x3f_70_);
    lean_dec_ref(v_inst_68_);
    v___x_71_ = lean_apply_1(v_succ_x3f_70_, v_a_69_);
    v_val_72_ = lean_ctor_get(v___x_71_, 0);
    lean_inc(v_val_72_);
    lean_dec(v___x_71_);
    return v_val_72_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succ(
    mut v_00_u03b1_73_: *mut LeanObject,
    mut v_inst_74_: *mut LeanObject,
    mut v_inst_75_: *mut LeanObject,
    mut v_a_76_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_79_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_77_ = lean_ctor_get(v_inst_74_, 0);
    lean_inc_ref(v_succ_x3f_77_);
    lean_dec_ref(v_inst_74_);
    v___x_78_ = lean_apply_1(v_succ_x3f_77_, v_a_76_);
    v_val_79_ = lean_ctor_get(v___x_78_, 0);
    lean_inc(v_val_79_);
    lean_dec(v___x_78_);
    return v_val_79_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succMany___redArg(
    mut v_inst_80_: *mut LeanObject,
    mut v_n_81_: *mut LeanObject,
    mut v_a_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succMany_x3f_83_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_85_: *mut LeanObject = core::ptr::null_mut();
    v_succMany_x3f_83_ = lean_ctor_get(v_inst_80_, 1);
    lean_inc_ref(v_succMany_x3f_83_);
    lean_dec_ref(v_inst_80_);
    v___x_84_ = lean_apply_2(v_succMany_x3f_83_, v_n_81_, v_a_82_);
    v_val_85_ = lean_ctor_get(v___x_84_, 0);
    lean_inc(v_val_85_);
    lean_dec(v___x_84_);
    return v_val_85_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succMany(
    mut v_00_u03b1_86_: *mut LeanObject,
    mut v_inst_87_: *mut LeanObject,
    mut v_inst_88_: *mut LeanObject,
    mut v_inst_89_: *mut LeanObject,
    mut v_n_90_: *mut LeanObject,
    mut v_a_91_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succMany_x3f_92_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_94_: *mut LeanObject = core::ptr::null_mut();
    v_succMany_x3f_92_ = lean_ctor_get(v_inst_87_, 1);
    lean_inc_ref(v_succMany_x3f_92_);
    lean_dec_ref(v_inst_87_);
    v___x_93_ = lean_apply_2(v_succMany_x3f_92_, v_n_90_, v_a_91_);
    v_val_94_ = lean_ctor_get(v___x_93_, 0);
    lean_inc(v_val_94_);
    lean_dec(v___x_93_);
    return v_val_94_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(
    mut v_00_u03b1_95_: *mut LeanObject,
    mut v_inst_96_: *mut LeanObject,
    mut v_inst_97_: *mut LeanObject,
    mut v_inst_98_: *mut LeanObject,
    mut v_inst_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    v___x_100_ = lean_box(0);
    return v___x_100_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___boxed(
    mut v_00_u03b1_101_: *mut LeanObject,
    mut v_inst_102_: *mut LeanObject,
    mut v_inst_103_: *mut LeanObject,
    mut v_inst_104_: *mut LeanObject,
    mut v_inst_105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_106_: *mut LeanObject = core::ptr::null_mut();
    v_res_106_ = l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(
        v_00_u03b1_101_,
        v_inst_102_,
        v_inst_103_,
        v_inst_104_,
        v_inst_105_,
    );
    lean_dec_ref(v_inst_103_);
    return v_res_106_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(
    mut v_00_u03b1_107_: *mut LeanObject,
    mut v_inst_108_: *mut LeanObject,
    mut v_inst_109_: *mut LeanObject,
    mut v_inst_110_: *mut LeanObject,
    mut v_inst_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    v___x_112_ = lean_box(0);
    return v___x_112_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___boxed(
    mut v_00_u03b1_113_: *mut LeanObject,
    mut v_inst_114_: *mut LeanObject,
    mut v_inst_115_: *mut LeanObject,
    mut v_inst_116_: *mut LeanObject,
    mut v_inst_117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_118_: *mut LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(
        v_00_u03b1_113_,
        v_inst_114_,
        v_inst_115_,
        v_inst_116_,
        v_inst_117_,
    );
    lean_dec_ref(v_inst_115_);
    return v_res_118_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___redArg(
    mut v_inst_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_120_: *mut LeanObject = core::ptr::null_mut();
    v_val_120_ = lean_ctor_get(v_inst_119_, 0);
    lean_inc(v_val_120_);
    return v_val_120_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___redArg___boxed(
    mut v_inst_121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_122_: *mut LeanObject = core::ptr::null_mut();
    v_res_122_ = l_Std_PRange_UpwardEnumerable_least___redArg(v_inst_121_);
    lean_dec(v_inst_121_);
    return v_res_122_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least(
    mut v_00_u03b1_123_: *mut LeanObject,
    mut v_inst_124_: *mut LeanObject,
    mut v_inst_125_: *mut LeanObject,
    mut v_inst_126_: *mut LeanObject,
    mut v_hn_127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_128_: *mut LeanObject = core::ptr::null_mut();
    v_val_128_ = lean_ctor_get(v_inst_125_, 0);
    lean_inc(v_val_128_);
    return v_val_128_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___boxed(
    mut v_00_u03b1_129_: *mut LeanObject,
    mut v_inst_130_: *mut LeanObject,
    mut v_inst_131_: *mut LeanObject,
    mut v_inst_132_: *mut LeanObject,
    mut v_hn_133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_134_: *mut LeanObject = core::ptr::null_mut();
    v_res_134_ = l_Std_PRange_UpwardEnumerable_least(
        v_00_u03b1_129_,
        v_inst_130_,
        v_inst_131_,
        v_inst_132_,
        v_hn_133_,
    );
    lean_dec(v_inst_131_);
    lean_dec_ref(v_inst_130_);
    return v_res_134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
}
