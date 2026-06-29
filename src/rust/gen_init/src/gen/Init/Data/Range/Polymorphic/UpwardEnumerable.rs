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
    mut v_inst_68_: *mut crate::leanh::LeanObject,
    mut v_a_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_70_ = crate::leanh::lean_ctor_get(v_inst_68_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_70_);
    crate::leanh::lean_dec_ref(v_inst_68_);
    v___x_71_ = crate::leanh::lean_apply_1(v_succ_x3f_70_, v_a_69_);
    v_val_72_ = crate::leanh::lean_ctor_get(v___x_71_, 0);
    crate::leanh::lean_inc(v_val_72_);
    crate::leanh::lean_dec(v___x_71_);
    return v_val_72_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succ(
    mut v_00_u03b1_73_: *mut crate::leanh::LeanObject,
    mut v_inst_74_: *mut crate::leanh::LeanObject,
    mut v_inst_75_: *mut crate::leanh::LeanObject,
    mut v_a_76_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_77_ = crate::leanh::lean_ctor_get(v_inst_74_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_77_);
    crate::leanh::lean_dec_ref(v_inst_74_);
    v___x_78_ = crate::leanh::lean_apply_1(v_succ_x3f_77_, v_a_76_);
    v_val_79_ = crate::leanh::lean_ctor_get(v___x_78_, 0);
    crate::leanh::lean_inc(v_val_79_);
    crate::leanh::lean_dec(v___x_78_);
    return v_val_79_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succMany___redArg(
    mut v_inst_80_: *mut crate::leanh::LeanObject,
    mut v_n_81_: *mut crate::leanh::LeanObject,
    mut v_a_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succMany_x3f_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succMany_x3f_83_ = crate::leanh::lean_ctor_get(v_inst_80_, 1);
    crate::leanh::lean_inc_ref(v_succMany_x3f_83_);
    crate::leanh::lean_dec_ref(v_inst_80_);
    v___x_84_ = crate::leanh::lean_apply_2(v_succMany_x3f_83_, v_n_81_, v_a_82_);
    v_val_85_ = crate::leanh::lean_ctor_get(v___x_84_, 0);
    crate::leanh::lean_inc(v_val_85_);
    crate::leanh::lean_dec(v___x_84_);
    return v_val_85_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_succMany(
    mut v_00_u03b1_86_: *mut crate::leanh::LeanObject,
    mut v_inst_87_: *mut crate::leanh::LeanObject,
    mut v_inst_88_: *mut crate::leanh::LeanObject,
    mut v_inst_89_: *mut crate::leanh::LeanObject,
    mut v_n_90_: *mut crate::leanh::LeanObject,
    mut v_a_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succMany_x3f_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succMany_x3f_92_ = crate::leanh::lean_ctor_get(v_inst_87_, 1);
    crate::leanh::lean_inc_ref(v_succMany_x3f_92_);
    crate::leanh::lean_dec_ref(v_inst_87_);
    v___x_93_ = crate::leanh::lean_apply_2(v_succMany_x3f_92_, v_n_90_, v_a_91_);
    v_val_94_ = crate::leanh::lean_ctor_get(v___x_93_, 0);
    crate::leanh::lean_inc(v_val_94_);
    crate::leanh::lean_dec(v___x_93_);
    return v_val_94_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(
    mut v_00_u03b1_95_: *mut crate::leanh::LeanObject,
    mut v_inst_96_: *mut crate::leanh::LeanObject,
    mut v_inst_97_: *mut crate::leanh::LeanObject,
    mut v_inst_98_: *mut crate::leanh::LeanObject,
    mut v_inst_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = crate::leanh::lean_box(0);
    return v___x_100_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___boxed(
    mut v_00_u03b1_101_: *mut crate::leanh::LeanObject,
    mut v_inst_102_: *mut crate::leanh::LeanObject,
    mut v_inst_103_: *mut crate::leanh::LeanObject,
    mut v_inst_104_: *mut crate::leanh::LeanObject,
    mut v_inst_105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_106_ = l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(
        v_00_u03b1_101_,
        v_inst_102_,
        v_inst_103_,
        v_inst_104_,
        v_inst_105_,
    );
    crate::leanh::lean_dec_ref(v_inst_103_);
    return v_res_106_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(
    mut v_00_u03b1_107_: *mut crate::leanh::LeanObject,
    mut v_inst_108_: *mut crate::leanh::LeanObject,
    mut v_inst_109_: *mut crate::leanh::LeanObject,
    mut v_inst_110_: *mut crate::leanh::LeanObject,
    mut v_inst_111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_112_ = crate::leanh::lean_box(0);
    return v___x_112_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___boxed(
    mut v_00_u03b1_113_: *mut crate::leanh::LeanObject,
    mut v_inst_114_: *mut crate::leanh::LeanObject,
    mut v_inst_115_: *mut crate::leanh::LeanObject,
    mut v_inst_116_: *mut crate::leanh::LeanObject,
    mut v_inst_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(
        v_00_u03b1_113_,
        v_inst_114_,
        v_inst_115_,
        v_inst_116_,
        v_inst_117_,
    );
    crate::leanh::lean_dec_ref(v_inst_115_);
    return v_res_118_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___redArg(
    mut v_inst_119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_120_ = crate::leanh::lean_ctor_get(v_inst_119_, 0);
    crate::leanh::lean_inc(v_val_120_);
    return v_val_120_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___redArg___boxed(
    mut v_inst_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = l_Std_PRange_UpwardEnumerable_least___redArg(v_inst_121_);
    crate::leanh::lean_dec(v_inst_121_);
    return v_res_122_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least(
    mut v_00_u03b1_123_: *mut crate::leanh::LeanObject,
    mut v_inst_124_: *mut crate::leanh::LeanObject,
    mut v_inst_125_: *mut crate::leanh::LeanObject,
    mut v_inst_126_: *mut crate::leanh::LeanObject,
    mut v_hn_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_128_ = crate::leanh::lean_ctor_get(v_inst_125_, 0);
    crate::leanh::lean_inc(v_val_128_);
    return v_val_128_;
}
pub unsafe fn l_Std_PRange_UpwardEnumerable_least___boxed(
    mut v_00_u03b1_129_: *mut crate::leanh::LeanObject,
    mut v_inst_130_: *mut crate::leanh::LeanObject,
    mut v_inst_131_: *mut crate::leanh::LeanObject,
    mut v_inst_132_: *mut crate::leanh::LeanObject,
    mut v_hn_133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_134_ = l_Std_PRange_UpwardEnumerable_least(
        v_00_u03b1_129_,
        v_inst_130_,
        v_inst_131_,
        v_inst_132_,
        v_hn_133_,
    );
    crate::leanh::lean_dec(v_inst_131_);
    crate::leanh::lean_dec_ref(v_inst_130_);
    return v_res_134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
}
