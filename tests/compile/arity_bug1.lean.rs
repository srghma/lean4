// Lean compiler output
// Module: arity_bug1
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Function_comp(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Function_const___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_instMonadEIO(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_Countdown_forM___redArg___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Countdown_forM___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Countdown_forM___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_Countdown_forM___redArg___closed__0_value) as *mut lean_object;
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 107, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_Countdown_ctorIdx(mut v_x_1_: u8) -> *mut lean_object{
if v_x_1_ == 0 {
let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); 
v___x_2_ = lean_unsigned_to_nat(0);
return v___x_2_;
} else {
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_unsigned_to_nat(1);
return v___x_3_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_ctorIdx___boxed(mut v_x_4_: *mut lean_object) -> *mut lean_object{
let mut v_x_boxed_5_: u8 = 0; let mut v_res_6_: *mut lean_object = core::ptr::null_mut(); 
v_x_boxed_5_ = (lean_unbox(v_x_4_) as u8);
v_res_6_ = l_Countdown_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_toCtorIdx(mut v_x_7_: u8) -> *mut lean_object{
let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); 
v___x_8_ = l_Countdown_ctorIdx(v_x_7_);
return v___x_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_toCtorIdx___boxed(mut v_x_9_: *mut lean_object) -> *mut lean_object{
let mut v_x_4__boxed_10_: u8 = 0; let mut v_res_11_: *mut lean_object = core::ptr::null_mut(); 
v_x_4__boxed_10_ = (lean_unbox(v_x_9_) as u8);
v_res_11_ = l_Countdown_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_ctorElim___redArg(mut v_k_12_: *mut lean_object) -> *mut lean_object{
lean_inc(v_k_12_);
return v_k_12_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_ctorElim___redArg___boxed(mut v_k_13_: *mut lean_object) -> *mut lean_object{
let mut v_res_14_: *mut lean_object = core::ptr::null_mut(); 
v_res_14_ = l_Countdown_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_ctorElim(mut v_motive_15_: *mut lean_object, mut v_ctorIdx_16_: *mut lean_object, mut v_t_17_: u8, mut v_h_18_: *mut lean_object, mut v_k_19_: *mut lean_object) -> *mut lean_object{
lean_inc(v_k_19_);
return v_k_19_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_ctorElim___boxed(mut v_motive_20_: *mut lean_object, mut v_ctorIdx_21_: *mut lean_object, mut v_t_22_: *mut lean_object, mut v_h_23_: *mut lean_object, mut v_k_24_: *mut lean_object) -> *mut lean_object{
let mut v_t_boxed_25_: u8 = 0; let mut v_res_26_: *mut lean_object = core::ptr::null_mut(); 
v_t_boxed_25_ = (lean_unbox(v_t_22_) as u8);
v_res_26_ = l_Countdown_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_zero_elim___redArg(mut v_zero_27_: *mut lean_object) -> *mut lean_object{
lean_inc(v_zero_27_);
return v_zero_27_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_zero_elim___redArg___boxed(mut v_zero_28_: *mut lean_object) -> *mut lean_object{
let mut v_res_29_: *mut lean_object = core::ptr::null_mut(); 
v_res_29_ = l_Countdown_zero_elim___redArg(v_zero_28_);
lean_dec(v_zero_28_);
return v_res_29_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_zero_elim(mut v_motive_30_: *mut lean_object, mut v_t_31_: u8, mut v_h_32_: *mut lean_object, mut v_zero_33_: *mut lean_object) -> *mut lean_object{
lean_inc(v_zero_33_);
return v_zero_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_zero_elim___boxed(mut v_motive_34_: *mut lean_object, mut v_t_35_: *mut lean_object, mut v_h_36_: *mut lean_object, mut v_zero_37_: *mut lean_object) -> *mut lean_object{
let mut v_t_boxed_38_: u8 = 0; let mut v_res_39_: *mut lean_object = core::ptr::null_mut(); 
v_t_boxed_38_ = (lean_unbox(v_t_35_) as u8);
v_res_39_ = l_Countdown_zero_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_zero_37_);
lean_dec(v_zero_37_);
return v_res_39_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_one_elim___redArg(mut v_one_40_: *mut lean_object) -> *mut lean_object{
lean_inc(v_one_40_);
return v_one_40_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_one_elim___redArg___boxed(mut v_one_41_: *mut lean_object) -> *mut lean_object{
let mut v_res_42_: *mut lean_object = core::ptr::null_mut(); 
v_res_42_ = l_Countdown_one_elim___redArg(v_one_41_);
lean_dec(v_one_41_);
return v_res_42_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_one_elim(mut v_motive_43_: *mut lean_object, mut v_t_44_: u8, mut v_h_45_: *mut lean_object, mut v_one_46_: *mut lean_object) -> *mut lean_object{
lean_inc(v_one_46_);
return v_one_46_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_one_elim___boxed(mut v_motive_47_: *mut lean_object, mut v_t_48_: *mut lean_object, mut v_h_49_: *mut lean_object, mut v_one_50_: *mut lean_object) -> *mut lean_object{
let mut v_t_boxed_51_: u8 = 0; let mut v_res_52_: *mut lean_object = core::ptr::null_mut(); 
v_t_boxed_51_ = (lean_unbox(v_t_48_) as u8);
v_res_52_ = l_Countdown_one_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_one_50_);
lean_dec(v_one_50_);
return v_res_52_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_run___redArg(mut v_x_53_: *mut lean_object, mut v_s_54_: *mut lean_object) -> *mut lean_object{
let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); 
v___x_55_ = lean_apply_1(v_x_53_, v_s_54_);
return v___x_55_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_run(mut v_00_u03c3_56_: *mut lean_object, mut v_m_57_: *mut lean_object, mut v_00_u03b1_58_: *mut lean_object, mut v_x_59_: *mut lean_object, mut v_s_60_: *mut lean_object) -> *mut lean_object{
let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); 
v___x_61_ = lean_apply_1(v_x_59_, v_s_60_);
return v___x_61_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_pure___redArg(mut v_inst_62_: *mut lean_object, mut v_a_63_: *mut lean_object, mut v_s_64_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_68_: u8 = 0; let mut v_toPure_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_73_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_74_: u8 = 0; let mut v_unused_75_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_65_ = lean_ctor_get(v_inst_62_, 0);
v_isSharedCheck_74_ = (!lean_is_exclusive(v_inst_62_)) as u8;
if v_isSharedCheck_74_ == 0 {
let mut v_unused_75_: *mut lean_object = core::ptr::null_mut(); 
v_unused_75_ = lean_ctor_get(v_inst_62_, 1);
lean_dec(v_unused_75_);
v___x_67_ = v_inst_62_;
v_isShared_68_ = v_isSharedCheck_74_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_65_);
lean_dec(v_inst_62_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_74_;
state = 1; continue;
}
}
1 => {
v_toPure_69_ = lean_ctor_get(v_toApplicative_65_, 1);
lean_inc(v_toPure_69_);
lean_dec_ref(v_toApplicative_65_);
if v_isShared_68_ == 0 {
lean_ctor_set(v___x_67_, 1, v_s_64_);
lean_ctor_set(v___x_67_, 0, v_a_63_);
v___x_71_ = v___x_67_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_73_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_63_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_s_64_);
v___x_71_ = v_reuseFailAlloc_73_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_pure(mut v_00_u03c3_76_: *mut lean_object, mut v_m_77_: *mut lean_object, mut v_inst_78_: *mut lean_object, mut v_00_u03b1_79_: *mut lean_object, mut v_a_80_: *mut lean_object, mut v_s_81_: *mut lean_object) -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = l_MyStateT_pure___redArg(v_inst_78_, v_a_80_, v_s_81_);
return v___x_82_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_bind___redArg___lam__0(mut v_f_83_: *mut lean_object, mut v_____x_84_: *mut lean_object) -> *mut lean_object{
let mut v_fst_85_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); 
v_fst_85_ = lean_ctor_get(v_____x_84_, 0);
lean_inc(v_fst_85_);
v_snd_86_ = lean_ctor_get(v_____x_84_, 1);
lean_inc(v_snd_86_);
lean_dec_ref(v_____x_84_);
v___x_87_ = lean_apply_2(v_f_83_, v_fst_85_, v_snd_86_);
return v___x_87_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_bind___redArg(mut v_inst_88_: *mut lean_object, mut v_x_89_: *mut lean_object, mut v_f_90_: *mut lean_object, mut v_s_91_: *mut lean_object) -> *mut lean_object{
let mut v_toBind_92_: *mut lean_object = core::ptr::null_mut(); let mut v___f_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); 
v_toBind_92_ = lean_ctor_get(v_inst_88_, 1);
lean_inc(v_toBind_92_);
lean_dec_ref(v_inst_88_);
v___f_93_ = lean_alloc_closure(l_MyStateT_bind___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_93_, 0, v_f_90_);
v___x_94_ = lean_apply_1(v_x_89_, v_s_91_);
v___x_95_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_94_, v___f_93_);
return v___x_95_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_bind(mut v_00_u03c3_96_: *mut lean_object, mut v_m_97_: *mut lean_object, mut v_inst_98_: *mut lean_object, mut v_00_u03b1_99_: *mut lean_object, mut v_00_u03b2_100_: *mut lean_object, mut v_x_101_: *mut lean_object, mut v_f_102_: *mut lean_object, mut v_s_103_: *mut lean_object) -> *mut lean_object{
let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); 
v___x_104_ = l_MyStateT_bind___redArg(v_inst_98_, v_x_101_, v_f_102_, v_s_103_);
return v___x_104_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__0(mut v_inst_105_: *mut lean_object, mut v_00_u03b1_106_: *mut lean_object, mut v_00_u03b2_107_: *mut lean_object, mut v_f_108_: *mut lean_object, mut v_x_109_: *mut lean_object, mut v___y_110_: *mut lean_object) -> *mut lean_object{
let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_inst_105_);
v___x_111_ = lean_alloc_closure(l_MyStateT_pure as *mut core::ffi::c_void, 6, 4);
lean_closure_set(v___x_111_, 0, lean_box(0));
lean_closure_set(v___x_111_, 1, lean_box(0));
lean_closure_set(v___x_111_, 2, v_inst_105_);
lean_closure_set(v___x_111_, 3, lean_box(0));
v___x_112_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
lean_closure_set(v___x_112_, 0, lean_box(0));
lean_closure_set(v___x_112_, 1, lean_box(0));
lean_closure_set(v___x_112_, 2, lean_box(0));
lean_closure_set(v___x_112_, 3, v___x_111_);
lean_closure_set(v___x_112_, 4, v_f_108_);
v___x_113_ = l_MyStateT_bind___redArg(v_inst_105_, v_x_109_, v___x_112_, v___y_110_);
return v___x_113_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__1(mut v_inst_114_: *mut lean_object, mut v_00_u03b1_115_: *mut lean_object, mut v_00_u03b2_116_: *mut lean_object, mut v___y_117_: *mut lean_object, mut v___y_118_: *mut lean_object, mut v___y_119_: *mut lean_object) -> *mut lean_object{
let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); 
v___x_120_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___x_120_, 0, lean_box(0));
lean_closure_set(v___x_120_, 1, lean_box(0));
lean_closure_set(v___x_120_, 2, v___y_117_);
lean_inc_ref(v_inst_114_);
v___x_121_ = lean_alloc_closure(l_MyStateT_pure as *mut core::ffi::c_void, 6, 4);
lean_closure_set(v___x_121_, 0, lean_box(0));
lean_closure_set(v___x_121_, 1, lean_box(0));
lean_closure_set(v___x_121_, 2, v_inst_114_);
lean_closure_set(v___x_121_, 3, lean_box(0));
v___x_122_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
lean_closure_set(v___x_122_, 0, lean_box(0));
lean_closure_set(v___x_122_, 1, lean_box(0));
lean_closure_set(v___x_122_, 2, lean_box(0));
lean_closure_set(v___x_122_, 3, v___x_121_);
lean_closure_set(v___x_122_, 4, v___x_120_);
v___x_123_ = l_MyStateT_bind___redArg(v_inst_114_, v___y_118_, v___x_122_, v___y_119_);
return v___x_123_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__2(mut v_x_124_: *mut lean_object, mut v_inst_125_: *mut lean_object, mut v_y_126_: *mut lean_object, mut v___y_127_: *mut lean_object) -> *mut lean_object{
let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); 
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_x_124_, v___x_128_);
lean_inc_ref(v_inst_125_);
v___x_130_ = lean_alloc_closure(l_MyStateT_pure as *mut core::ffi::c_void, 6, 4);
lean_closure_set(v___x_130_, 0, lean_box(0));
lean_closure_set(v___x_130_, 1, lean_box(0));
lean_closure_set(v___x_130_, 2, v_inst_125_);
lean_closure_set(v___x_130_, 3, lean_box(0));
v___x_131_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
lean_closure_set(v___x_131_, 0, lean_box(0));
lean_closure_set(v___x_131_, 1, lean_box(0));
lean_closure_set(v___x_131_, 2, lean_box(0));
lean_closure_set(v___x_131_, 3, v___x_130_);
lean_closure_set(v___x_131_, 4, v_y_126_);
v___x_132_ = l_MyStateT_bind___redArg(v_inst_125_, v___x_129_, v___x_131_, v___y_127_);
return v___x_132_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__3(mut v_inst_133_: *mut lean_object, mut v_00_u03b1_134_: *mut lean_object, mut v_00_u03b2_135_: *mut lean_object, mut v_f_136_: *mut lean_object, mut v_x_137_: *mut lean_object, mut v___y_138_: *mut lean_object) -> *mut lean_object{
let mut v___f_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_inst_133_);
v___f_139_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__2 as *mut core::ffi::c_void, 4, 2);
lean_closure_set(v___f_139_, 0, v_x_137_);
lean_closure_set(v___f_139_, 1, v_inst_133_);
v___x_140_ = l_MyStateT_bind___redArg(v_inst_133_, v_f_136_, v___f_139_, v___y_138_);
return v___x_140_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__4(mut v_inst_141_: *mut lean_object, mut v_a_142_: *mut lean_object, mut v_x_143_: *mut lean_object, mut v___y_144_: *mut lean_object) -> *mut lean_object{
let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); 
v___x_145_ = l_MyStateT_pure___redArg(v_inst_141_, v_a_142_, v___y_144_);
return v___x_145_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__4___boxed(mut v_inst_146_: *mut lean_object, mut v_a_147_: *mut lean_object, mut v_x_148_: *mut lean_object, mut v___y_149_: *mut lean_object) -> *mut lean_object{
let mut v_res_150_: *mut lean_object = core::ptr::null_mut(); 
v_res_150_ = l_MyStateT_instMonad___redArg___lam__4(v_inst_146_, v_a_147_, v_x_148_, v___y_149_);
lean_dec(v_x_148_);
return v_res_150_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__5(mut v_inst_151_: *mut lean_object, mut v_y_152_: *mut lean_object, mut v_a_153_: *mut lean_object, mut v___y_154_: *mut lean_object) -> *mut lean_object{
let mut v___f_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_inst_151_);
v___f_155_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__4___boxed as *mut core::ffi::c_void, 4, 2);
lean_closure_set(v___f_155_, 0, v_inst_151_);
lean_closure_set(v___f_155_, 1, v_a_153_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_apply_1(v_y_152_, v___x_156_);
v___x_158_ = l_MyStateT_bind___redArg(v_inst_151_, v___x_157_, v___f_155_, v___y_154_);
return v___x_158_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__6(mut v_inst_159_: *mut lean_object, mut v_00_u03b1_160_: *mut lean_object, mut v_00_u03b2_161_: *mut lean_object, mut v_x_162_: *mut lean_object, mut v_y_163_: *mut lean_object, mut v___y_164_: *mut lean_object) -> *mut lean_object{
let mut v___f_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_inst_159_);
v___f_165_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void, 4, 2);
lean_closure_set(v___f_165_, 0, v_inst_159_);
lean_closure_set(v___f_165_, 1, v_y_163_);
v___x_166_ = l_MyStateT_bind___redArg(v_inst_159_, v_x_162_, v___f_165_, v___y_164_);
return v___x_166_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__7(mut v_y_167_: *mut lean_object, mut v_x_168_: *mut lean_object, mut v___y_169_: *mut lean_object) -> *mut lean_object{
let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); 
v___x_170_ = lean_box(0);
v___x_171_ = lean_apply_2(v_y_167_, v___x_170_, v___y_169_);
return v___x_171_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__7___boxed(mut v_y_172_: *mut lean_object, mut v_x_173_: *mut lean_object, mut v___y_174_: *mut lean_object) -> *mut lean_object{
let mut v_res_175_: *mut lean_object = core::ptr::null_mut(); 
v_res_175_ = l_MyStateT_instMonad___redArg___lam__7(v_y_172_, v_x_173_, v___y_174_);
lean_dec(v_x_173_);
return v_res_175_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg___lam__8(mut v_inst_176_: *mut lean_object, mut v_00_u03b1_177_: *mut lean_object, mut v_00_u03b2_178_: *mut lean_object, mut v_x_179_: *mut lean_object, mut v_y_180_: *mut lean_object, mut v___y_181_: *mut lean_object) -> *mut lean_object{
let mut v___f_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_183_: *mut lean_object = core::ptr::null_mut(); 
v___f_182_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__7___boxed as *mut core::ffi::c_void, 3, 1);
lean_closure_set(v___f_182_, 0, v_y_180_);
v___x_183_ = l_MyStateT_bind___redArg(v_inst_176_, v_x_179_, v___f_182_, v___y_181_);
return v___x_183_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad___redArg(mut v_inst_184_: *mut lean_object) -> *mut lean_object{
let mut v___f_185_: *mut lean_object = core::ptr::null_mut(); let mut v___f_186_: *mut lean_object = core::ptr::null_mut(); let mut v___f_187_: *mut lean_object = core::ptr::null_mut(); let mut v___f_188_: *mut lean_object = core::ptr::null_mut(); let mut v___f_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v___x_193_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref_n(v_inst_184_, 6);
v___f_185_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__0 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_185_, 0, v_inst_184_);
v___f_186_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_186_, 0, v_inst_184_);
v___f_187_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_187_, 0, v_inst_184_);
v___f_188_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__6 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_188_, 0, v_inst_184_);
v___f_189_ = lean_alloc_closure(l_MyStateT_instMonad___redArg___lam__8 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_189_, 0, v_inst_184_);
v___x_190_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_190_, 0, v___f_185_);
lean_ctor_set(v___x_190_, 1, v___f_186_);
v___x_191_ = lean_alloc_closure(l_MyStateT_pure as *mut core::ffi::c_void, 6, 3);
lean_closure_set(v___x_191_, 0, lean_box(0));
lean_closure_set(v___x_191_, 1, lean_box(0));
lean_closure_set(v___x_191_, 2, v_inst_184_);
v___x_192_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
lean_ctor_set(v___x_192_, 2, v___f_187_);
lean_ctor_set(v___x_192_, 3, v___f_188_);
lean_ctor_set(v___x_192_, 4, v___f_189_);
v___x_193_ = lean_alloc_closure(l_MyStateT_bind as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_193_, 0, lean_box(0));
lean_closure_set(v___x_193_, 1, lean_box(0));
lean_closure_set(v___x_193_, 2, v_inst_184_);
v___x_194_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
return v___x_194_;
}
#[no_mangle] pub unsafe extern "C" fn l_MyStateT_instMonad(mut v_00_u03c3_195_: *mut lean_object, mut v_m_196_: *mut lean_object, mut v_inst_197_: *mut lean_object) -> *mut lean_object{
let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); 
v___x_198_ = l_MyStateT_instMonad___redArg(v_inst_197_);
return v___x_198_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_forM___redArg___lam__0(mut v_x_199_: *mut lean_object) -> *mut lean_object{
let mut v_fst_200_: *mut lean_object = core::ptr::null_mut(); 
v_fst_200_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_fst_200_);
return v_fst_200_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_forM___redArg___lam__0___boxed(mut v_x_201_: *mut lean_object) -> *mut lean_object{
let mut v_res_202_: *mut lean_object = core::ptr::null_mut(); 
v_res_202_ = l_Countdown_forM___redArg___lam__0(v_x_201_);
lean_dec_ref(v_x_201_);
return v_res_202_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_forM___redArg(mut v_inst_204_: *mut lean_object, mut v_c_205_: u8) -> *mut lean_object{
let mut v_toApplicative_206_: *mut lean_object = core::ptr::null_mut(); let mut v_toFunctor_207_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_206_ = lean_ctor_get(v_inst_204_, 0);
v_toFunctor_207_ = lean_ctor_get(v_toApplicative_206_, 0);
lean_inc_ref(v_toFunctor_207_);
v_toPure_208_ = lean_ctor_get(v_toApplicative_206_, 1);
lean_inc(v_toPure_208_);
v___x_209_ = l_MyStateT_instMonad___redArg(v_inst_204_);
if v_c_205_ == 0 {
let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v___x_209_);
lean_dec_ref(v_toFunctor_207_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_apply_2(v_toPure_208_, lean_box(0), v___x_210_);
return v___x_211_;
} else {
let mut v_map_212_: *mut lean_object = core::ptr::null_mut(); let mut v___f_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: u8 = 0; let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43__overap_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_toPure_208_);
v_map_212_ = lean_ctor_get(v_toFunctor_207_, 0);
lean_inc(v_map_212_);
lean_dec_ref(v_toFunctor_207_);
v___f_213_ = l_Countdown_forM___redArg___closed__0;
v___x_214_ = 0;
v___x_215_ = lean_box(0);
v___x_43__overap_216_ = l_Countdown_forM___redArg(v___x_209_, v___x_214_);
v___x_217_ = lean_apply_1(v___x_43__overap_216_, v___x_215_);
v___x_218_ = lean_apply_4(v_map_212_, lean_box(0), lean_box(0), v___f_213_, v___x_217_);
return v___x_218_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_forM___redArg___boxed(mut v_inst_219_: *mut lean_object, mut v_c_220_: *mut lean_object) -> *mut lean_object{
let mut v_c_boxed_221_: u8 = 0; let mut v_res_222_: *mut lean_object = core::ptr::null_mut(); 
v_c_boxed_221_ = (lean_unbox(v_c_220_) as u8);
v_res_222_ = l_Countdown_forM___redArg(v_inst_219_, v_c_boxed_221_);
return v_res_222_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_forM(mut v_m_223_: *mut lean_object, mut v_inst_224_: *mut lean_object, mut v_c_225_: u8) -> *mut lean_object{
let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); 
v___x_226_ = l_Countdown_forM___redArg(v_inst_224_, v_c_225_);
return v___x_226_;
}
#[no_mangle] pub unsafe extern "C" fn l_Countdown_forM___boxed(mut v_m_227_: *mut lean_object, mut v_inst_228_: *mut lean_object, mut v_c_229_: *mut lean_object) -> *mut lean_object{
let mut v_c_boxed_230_: u8 = 0; let mut v_res_231_: *mut lean_object = core::ptr::null_mut(); 
v_c_boxed_230_ = (lean_unbox(v_c_229_) as u8);
v_res_231_ = l_Countdown_forM(v_m_227_, v_inst_228_, v_c_boxed_230_);
return v_res_231_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_232_: *mut lean_object) -> *mut lean_object{
let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_235_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); 
v___x_234_ = lean_get_stdout();
v_putStr_235_ = lean_ctor_get(v___x_234_, 4);
lean_inc_ref(v_putStr_235_);
lean_dec_ref(v___x_234_);
v___x_236_ = lean_apply_2(v_putStr_235_, v_s_232_, lean_box(0));
return v___x_236_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_237_: *mut lean_object, mut v_a_238_: *mut lean_object) -> *mut lean_object{
let mut v_res_239_: *mut lean_object = core::ptr::null_mut(); 
v_res_239_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_237_);
return v_res_239_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_240_: *mut lean_object) -> *mut lean_object{
let mut v___x_242_: u32 = 0; let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); 
v___x_242_ = 10;
v___x_243_ = lean_string_push(v_s_240_, v___x_242_);
v___x_244_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_243_);
return v___x_244_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_245_: *mut lean_object, mut v_a_246_: *mut lean_object) -> *mut lean_object{
let mut v_res_247_: *mut lean_object = core::ptr::null_mut(); 
v_res_247_ = l_IO_println___at___00main_spec__0(v_s_245_);
return v_res_247_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); 
v___x_248_ = l_instMonadEIO(lean_box(0));
return v___x_248_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: u8 = 0; let mut v___x_31__overap_253_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); 
v___x_251_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_252_ = 1;
v___x_31__overap_253_ = l_Countdown_forM___redArg(v___x_251_, v___x_252_);
v___x_254_ = lean_apply_1(v___x_31__overap_253_, lean_box(0));
if lean_obj_tag(v___x_254_) == 0 {
let mut v___x_255_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_254_, 1);
v___x_255_ = l_main___closed__1;
v___x_256_ = l_IO_println___at___00main_spec__0(v___x_255_);
return v___x_256_;
} else {
return v___x_254_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_257_: *mut lean_object) -> *mut lean_object{
let mut v_res_258_: *mut lean_object = core::ptr::null_mut(); 
v_res_258_ = _lean_main();
return v_res_258_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_arity__bug1(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_arity__bug1(1 /* builtin */);
  lean_io_mark_end_initialization();
  let mut ret_val = 1;
  if lean_io_result_is_ok(res) {
    lean_dec(res);
    lean_init_task_manager();
    let main_res = lean_run_main(run_main, argc, argv);
    lean_finalize_task_manager();
    if lean_io_result_is_ok(main_res) {
      ret_val = 0;
      lean_dec(main_res);
    } else {
      lean_io_result_show_error(main_res);
      lean_dec(main_res);
    }
  } else {
    lean_io_result_show_error(res);
    lean_dec(res);
  }
  return ret_val;
}
