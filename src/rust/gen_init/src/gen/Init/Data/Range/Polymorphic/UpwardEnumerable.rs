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
pub unsafe fn l_Std_PRange_UpwardEnumerable_succ___redArg(
    mut v_inst_68_: *mut leanh::LeanObject,
    mut v_a_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_succ_x3f_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_70_ = leanh::lean_ctor_get(v_inst_68_, 0);
    leanh::lean_inc_ref(v_succ_x3f_70_);
    leanh::lean_dec_ref(v_inst_68_);
    v___x_71_ = leanh::lean_apply_1(v_succ_x3f_70_, v_a_69_);
    v_val_72_ = leanh::lean_ctor_get(v___x_71_, 0);
    leanh::lean_inc(v_val_72_);
    leanh::lean_dec(v___x_71_);
    return v_val_72_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succ(
    mut v_00_u03b1_73_: *mut leanh::LeanObject,
    mut v_inst_74_: *mut leanh::LeanObject,
    mut v_inst_75_: *mut leanh::LeanObject,
    mut v_a_76_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_succ_x3f_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_77_ = leanh::lean_ctor_get(v_inst_74_, 0);
    leanh::lean_inc_ref(v_succ_x3f_77_);
    leanh::lean_dec_ref(v_inst_74_);
    v___x_78_ = leanh::lean_apply_1(v_succ_x3f_77_, v_a_76_);
    v_val_79_ = leanh::lean_ctor_get(v___x_78_, 0);
    leanh::lean_inc(v_val_79_);
    leanh::lean_dec(v___x_78_);
    return v_val_79_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succMany___redArg(
    mut v_inst_80_: *mut leanh::LeanObject,
    mut v_n_81_: *mut leanh::LeanObject,
    mut v_a_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_succMany_x3f_83_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_85_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_succMany_x3f_83_ = leanh::lean_ctor_get(v_inst_80_, 1);
    leanh::lean_inc_ref(v_succMany_x3f_83_);
    leanh::lean_dec_ref(v_inst_80_);
    v___x_84_ = leanh::lean_apply_2(v_succMany_x3f_83_, v_n_81_, v_a_82_);
    v_val_85_ = leanh::lean_ctor_get(v___x_84_, 0);
    leanh::lean_inc(v_val_85_);
    leanh::lean_dec(v___x_84_);
    return v_val_85_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succMany(
    mut v_00_u03b1_86_: *mut leanh::LeanObject,
    mut v_inst_87_: *mut leanh::LeanObject,
    mut v_inst_88_: *mut leanh::LeanObject,
    mut v_inst_89_: *mut leanh::LeanObject,
    mut v_n_90_: *mut leanh::LeanObject,
    mut v_a_91_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_succMany_x3f_92_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_succMany_x3f_92_ = leanh::lean_ctor_get(v_inst_87_, 1);
    leanh::lean_inc_ref(v_succMany_x3f_92_);
    leanh::lean_dec_ref(v_inst_87_);
    v___x_93_ = leanh::lean_apply_2(v_succMany_x3f_92_, v_n_90_, v_a_91_);
    v_val_94_ = leanh::lean_ctor_get(v___x_93_, 0);
    leanh::lean_inc(v_val_94_);
    leanh::lean_dec(v___x_93_);
    return v_val_94_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(
    mut v_00_u03b1_95_: *mut leanh::LeanObject,
    mut v_inst_96_: *mut leanh::LeanObject,
    mut v_inst_97_: *mut leanh::LeanObject,
    mut v_inst_98_: *mut leanh::LeanObject,
    mut v_inst_99_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = leanh::lean_box(0);
    return v___x_100_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___boxed(
    mut v_00_u03b1_101_: *mut leanh::LeanObject,
    mut v_inst_102_: *mut leanh::LeanObject,
    mut v_inst_103_: *mut leanh::LeanObject,
    mut v_inst_104_: *mut leanh::LeanObject,
    mut v_inst_105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_106_ = l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(
        v_00_u03b1_101_,
        v_inst_102_,
        v_inst_103_,
        v_inst_104_,
        v_inst_105_,
    );
    leanh::lean_dec_ref(v_inst_103_);
    return v_res_106_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(
    mut v_00_u03b1_107_: *mut leanh::LeanObject,
    mut v_inst_108_: *mut leanh::LeanObject,
    mut v_inst_109_: *mut leanh::LeanObject,
    mut v_inst_110_: *mut leanh::LeanObject,
    mut v_inst_111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_112_ = leanh::lean_box(0);
    return v___x_112_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___boxed(
    mut v_00_u03b1_113_: *mut leanh::LeanObject,
    mut v_inst_114_: *mut leanh::LeanObject,
    mut v_inst_115_: *mut leanh::LeanObject,
    mut v_inst_116_: *mut leanh::LeanObject,
    mut v_inst_117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(
        v_00_u03b1_113_,
        v_inst_114_,
        v_inst_115_,
        v_inst_116_,
        v_inst_117_,
    );
    leanh::lean_dec_ref(v_inst_115_);
    return v_res_118_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___redArg(
    mut v_inst_119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_120_ = leanh::lean_ctor_get(v_inst_119_, 0);
    leanh::lean_inc(v_val_120_);
    return v_val_120_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___redArg___boxed(
    mut v_inst_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = l_Std_PRange_UpwardEnumerable_least___redArg(v_inst_121_);
    leanh::lean_dec(v_inst_121_);
    return v_res_122_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least(
    mut v_00_u03b1_123_: *mut leanh::LeanObject,
    mut v_inst_124_: *mut leanh::LeanObject,
    mut v_inst_125_: *mut leanh::LeanObject,
    mut v_inst_126_: *mut leanh::LeanObject,
    mut v_hn_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_128_ = leanh::lean_ctor_get(v_inst_125_, 0);
    leanh::lean_inc(v_val_128_);
    return v_val_128_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___boxed(
    mut v_00_u03b1_129_: *mut leanh::LeanObject,
    mut v_inst_130_: *mut leanh::LeanObject,
    mut v_inst_131_: *mut leanh::LeanObject,
    mut v_inst_132_: *mut leanh::LeanObject,
    mut v_hn_133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_134_ = l_Std_PRange_UpwardEnumerable_least(
        v_00_u03b1_129_,
        v_inst_130_,
        v_inst_131_,
        v_inst_132_,
        v_hn_133_,
    );
    leanh::lean_dec(v_inst_131_);
    leanh::lean_dec_ref(v_inst_130_);
    return v_res_134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Classes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
}