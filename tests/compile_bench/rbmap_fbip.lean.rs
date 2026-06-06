// Lean compiler output
// Module: rbmap_fbip
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_List_head_x21___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_main___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_Color_ctorIdx(mut v_x_1_: u8) -> *mut lean_object{
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
#[no_mangle] pub unsafe extern "C" fn l_Color_ctorIdx___boxed(mut v_x_4_: *mut lean_object) -> *mut lean_object{
let mut v_x_boxed_5_: u8 = 0; let mut v_res_6_: *mut lean_object = core::ptr::null_mut(); 
v_x_boxed_5_ = (lean_unbox(v_x_4_) as u8);
v_res_6_ = l_Color_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_toCtorIdx(mut v_x_7_: u8) -> *mut lean_object{
let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); 
v___x_8_ = l_Color_ctorIdx(v_x_7_);
return v___x_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_toCtorIdx___boxed(mut v_x_9_: *mut lean_object) -> *mut lean_object{
let mut v_x_4__boxed_10_: u8 = 0; let mut v_res_11_: *mut lean_object = core::ptr::null_mut(); 
v_x_4__boxed_10_ = (lean_unbox(v_x_9_) as u8);
v_res_11_ = l_Color_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_ctorElim___redArg(mut v_k_12_: *mut lean_object) -> *mut lean_object{
lean_inc(v_k_12_);
return v_k_12_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_ctorElim___redArg___boxed(mut v_k_13_: *mut lean_object) -> *mut lean_object{
let mut v_res_14_: *mut lean_object = core::ptr::null_mut(); 
v_res_14_ = l_Color_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_ctorElim(mut v_motive_15_: *mut lean_object, mut v_ctorIdx_16_: *mut lean_object, mut v_t_17_: u8, mut v_h_18_: *mut lean_object, mut v_k_19_: *mut lean_object) -> *mut lean_object{
lean_inc(v_k_19_);
return v_k_19_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_ctorElim___boxed(mut v_motive_20_: *mut lean_object, mut v_ctorIdx_21_: *mut lean_object, mut v_t_22_: *mut lean_object, mut v_h_23_: *mut lean_object, mut v_k_24_: *mut lean_object) -> *mut lean_object{
let mut v_t_boxed_25_: u8 = 0; let mut v_res_26_: *mut lean_object = core::ptr::null_mut(); 
v_t_boxed_25_ = (lean_unbox(v_t_22_) as u8);
v_res_26_ = l_Color_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_red_elim___redArg(mut v_red_27_: *mut lean_object) -> *mut lean_object{
lean_inc(v_red_27_);
return v_red_27_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_red_elim___redArg___boxed(mut v_red_28_: *mut lean_object) -> *mut lean_object{
let mut v_res_29_: *mut lean_object = core::ptr::null_mut(); 
v_res_29_ = l_Color_red_elim___redArg(v_red_28_);
lean_dec(v_red_28_);
return v_res_29_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_red_elim(mut v_motive_30_: *mut lean_object, mut v_t_31_: u8, mut v_h_32_: *mut lean_object, mut v_red_33_: *mut lean_object) -> *mut lean_object{
lean_inc(v_red_33_);
return v_red_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_red_elim___boxed(mut v_motive_34_: *mut lean_object, mut v_t_35_: *mut lean_object, mut v_h_36_: *mut lean_object, mut v_red_37_: *mut lean_object) -> *mut lean_object{
let mut v_t_boxed_38_: u8 = 0; let mut v_res_39_: *mut lean_object = core::ptr::null_mut(); 
v_t_boxed_38_ = (lean_unbox(v_t_35_) as u8);
v_res_39_ = l_Color_red_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_red_37_);
lean_dec(v_red_37_);
return v_res_39_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_black_elim___redArg(mut v_black_40_: *mut lean_object) -> *mut lean_object{
lean_inc(v_black_40_);
return v_black_40_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_black_elim___redArg___boxed(mut v_black_41_: *mut lean_object) -> *mut lean_object{
let mut v_res_42_: *mut lean_object = core::ptr::null_mut(); 
v_res_42_ = l_Color_black_elim___redArg(v_black_41_);
lean_dec(v_black_41_);
return v_res_42_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_black_elim(mut v_motive_43_: *mut lean_object, mut v_t_44_: u8, mut v_h_45_: *mut lean_object, mut v_black_46_: *mut lean_object) -> *mut lean_object{
lean_inc(v_black_46_);
return v_black_46_;
}
#[no_mangle] pub unsafe extern "C" fn l_Color_black_elim___boxed(mut v_motive_47_: *mut lean_object, mut v_t_48_: *mut lean_object, mut v_h_49_: *mut lean_object, mut v_black_50_: *mut lean_object) -> *mut lean_object{
let mut v_t_boxed_51_: u8 = 0; let mut v_res_52_: *mut lean_object = core::ptr::null_mut(); 
v_t_boxed_51_ = (lean_unbox(v_t_48_) as u8);
v_res_52_ = l_Color_black_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_black_50_);
lean_dec(v_black_50_);
return v_res_52_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorIdx(mut v_x_53_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_53_) == 0 {
let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); 
v___x_54_ = lean_unsigned_to_nat(0);
return v___x_54_;
} else {
let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); 
v___x_55_ = lean_unsigned_to_nat(1);
return v___x_55_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorIdx___boxed(mut v_x_56_: *mut lean_object) -> *mut lean_object{
let mut v_res_57_: *mut lean_object = core::ptr::null_mut(); 
v_res_57_ = l_Tree_ctorIdx(v_x_56_);
lean_dec(v_x_56_);
return v_res_57_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorElim___redArg(mut v_t_58_: *mut lean_object, mut v_k_59_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_t_58_) == 0 {
return v_k_59_;
} else {
let mut v_a_60_: u8 = 0; let mut v_a_61_: *mut lean_object = core::ptr::null_mut(); let mut v_a_62_: *mut lean_object = core::ptr::null_mut(); let mut v_a_63_: u8 = 0; let mut v_a_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v_a_60_ = lean_ctor_get_uint8(v_t_58_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
v_a_61_ = lean_ctor_get(v_t_58_, 0);
lean_inc(v_a_61_);
v_a_62_ = lean_ctor_get(v_t_58_, 1);
lean_inc(v_a_62_);
v_a_63_ = lean_ctor_get_uint8(v_t_58_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_64_ = lean_ctor_get(v_t_58_, 2);
lean_inc(v_a_64_);
lean_dec_ref_known(v_t_58_, 3);
v___x_65_ = lean_box((v_a_60_) as usize);
v___x_66_ = lean_box((v_a_63_) as usize);
v___x_67_ = lean_apply_5(v_k_59_, v___x_65_, v_a_61_, v_a_62_, v___x_66_, v_a_64_);
return v___x_67_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorElim(mut v_motive_68_: *mut lean_object, mut v_ctorIdx_69_: *mut lean_object, mut v_t_70_: *mut lean_object, mut v_h_71_: *mut lean_object, mut v_k_72_: *mut lean_object) -> *mut lean_object{
let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); 
v___x_73_ = l_Tree_ctorElim___redArg(v_t_70_, v_k_72_);
return v___x_73_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorElim___boxed(mut v_motive_74_: *mut lean_object, mut v_ctorIdx_75_: *mut lean_object, mut v_t_76_: *mut lean_object, mut v_h_77_: *mut lean_object, mut v_k_78_: *mut lean_object) -> *mut lean_object{
let mut v_res_79_: *mut lean_object = core::ptr::null_mut(); 
v_res_79_ = l_Tree_ctorElim(v_motive_74_, v_ctorIdx_75_, v_t_76_, v_h_77_, v_k_78_);
lean_dec(v_ctorIdx_75_);
return v_res_79_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_leaf_elim___redArg(mut v_t_80_: *mut lean_object, mut v_leaf_81_: *mut lean_object) -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = l_Tree_ctorElim___redArg(v_t_80_, v_leaf_81_);
return v___x_82_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_leaf_elim(mut v_motive_83_: *mut lean_object, mut v_t_84_: *mut lean_object, mut v_h_85_: *mut lean_object, mut v_leaf_86_: *mut lean_object) -> *mut lean_object{
let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); 
v___x_87_ = l_Tree_ctorElim___redArg(v_t_84_, v_leaf_86_);
return v___x_87_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_node_elim___redArg(mut v_t_88_: *mut lean_object, mut v_node_89_: *mut lean_object) -> *mut lean_object{
let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); 
v___x_90_ = l_Tree_ctorElim___redArg(v_t_88_, v_node_89_);
return v___x_90_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_node_elim(mut v_motive_91_: *mut lean_object, mut v_t_92_: *mut lean_object, mut v_h_93_: *mut lean_object, mut v_node_94_: *mut lean_object) -> *mut lean_object{
let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); 
v___x_95_ = l_Tree_ctorElim___redArg(v_t_92_, v_node_94_);
return v___x_95_;
}
#[no_mangle] pub unsafe extern "C" fn l_fold___redArg(mut v_f_96_: *mut lean_object, mut v_x_97_: *mut lean_object, mut v_x_98_: *mut lean_object) -> *mut lean_object{
let mut v_a_99_: *mut lean_object = core::ptr::null_mut(); let mut v_a_100_: *mut lean_object = core::ptr::null_mut(); let mut v_a_101_: u8 = 0; let mut v_a_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_97_) == 0 {
lean_dec(v_f_96_);
return v_x_98_;
} else {
let mut v_a_99_: *mut lean_object = core::ptr::null_mut(); let mut v_a_100_: *mut lean_object = core::ptr::null_mut(); let mut v_a_101_: u8 = 0; let mut v_a_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); 
v_a_99_ = lean_ctor_get(v_x_97_, 0);
lean_inc(v_a_99_);
v_a_100_ = lean_ctor_get(v_x_97_, 1);
lean_inc(v_a_100_);
v_a_101_ = lean_ctor_get_uint8(v_x_97_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_102_ = lean_ctor_get(v_x_97_, 2);
lean_inc(v_a_102_);
lean_dec_ref_known(v_x_97_, 3);
lean_inc_n(v_f_96_, 2);
v___x_103_ = l_fold___redArg(v_f_96_, v_a_99_, v_x_98_);
v___x_104_ = lean_box((v_a_101_) as usize);
v___x_105_ = lean_apply_3(v_f_96_, v_a_100_, v___x_104_, v___x_103_);
v_x_97_ = v_a_102_;
v_x_98_ = v___x_105_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_fold(mut v_00_u03c3_107_: *mut lean_object, mut v_f_108_: *mut lean_object, mut v_x_109_: *mut lean_object, mut v_x_110_: *mut lean_object) -> *mut lean_object{
let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
v___x_111_ = l_fold___redArg(v_f_108_, v_x_109_, v_x_110_);
return v___x_111_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_ctorIdx(mut v_x_112_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_112_)
{
0 => {
let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); 
v___x_113_ = lean_unsigned_to_nat(0);
return v___x_113_;
}
1 => {
let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); 
v___x_114_ = lean_unsigned_to_nat(1);
return v___x_114_;
}
_ => {
let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); 
v___x_115_ = lean_unsigned_to_nat(2);
return v___x_115_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_ctorIdx___boxed(mut v_x_116_: *mut lean_object) -> *mut lean_object{
let mut v_res_117_: *mut lean_object = core::ptr::null_mut(); 
v_res_117_ = l_Tree_Zipper_ctorIdx(v_x_116_);
lean_dec(v_x_116_);
return v_res_117_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_ctorElim___redArg(mut v_t_118_: *mut lean_object, mut v_k_119_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_t_118_) == 2 {
return v_k_119_;
} else {
let mut v_a_120_: u8 = 0; let mut v_a_121_: *mut lean_object = core::ptr::null_mut(); let mut v_a_122_: *mut lean_object = core::ptr::null_mut(); let mut v_a_123_: u8 = 0; let mut v_a_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); 
v_a_120_ = lean_ctor_get_uint8(v_t_118_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
v_a_121_ = lean_ctor_get(v_t_118_, 0);
lean_inc(v_a_121_);
v_a_122_ = lean_ctor_get(v_t_118_, 1);
lean_inc(v_a_122_);
v_a_123_ = lean_ctor_get_uint8(v_t_118_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_124_ = lean_ctor_get(v_t_118_, 2);
lean_inc(v_a_124_);
lean_dec(v_t_118_);
v___x_125_ = lean_box((v_a_120_) as usize);
v___x_126_ = lean_box((v_a_123_) as usize);
v___x_127_ = lean_apply_5(v_k_119_, v___x_125_, v_a_121_, v_a_122_, v___x_126_, v_a_124_);
return v___x_127_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_ctorElim(mut v_motive_128_: *mut lean_object, mut v_ctorIdx_129_: *mut lean_object, mut v_t_130_: *mut lean_object, mut v_h_131_: *mut lean_object, mut v_k_132_: *mut lean_object) -> *mut lean_object{
let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); 
v___x_133_ = l_Tree_Zipper_ctorElim___redArg(v_t_130_, v_k_132_);
return v___x_133_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_ctorElim___boxed(mut v_motive_134_: *mut lean_object, mut v_ctorIdx_135_: *mut lean_object, mut v_t_136_: *mut lean_object, mut v_h_137_: *mut lean_object, mut v_k_138_: *mut lean_object) -> *mut lean_object{
let mut v_res_139_: *mut lean_object = core::ptr::null_mut(); 
v_res_139_ = l_Tree_Zipper_ctorElim(v_motive_134_, v_ctorIdx_135_, v_t_136_, v_h_137_, v_k_138_);
lean_dec(v_ctorIdx_135_);
return v_res_139_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_nodeR_elim___redArg(mut v_t_140_: *mut lean_object, mut v_nodeR_141_: *mut lean_object) -> *mut lean_object{
let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); 
v___x_142_ = l_Tree_Zipper_ctorElim___redArg(v_t_140_, v_nodeR_141_);
return v___x_142_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_nodeR_elim(mut v_motive_143_: *mut lean_object, mut v_t_144_: *mut lean_object, mut v_h_145_: *mut lean_object, mut v_nodeR_146_: *mut lean_object) -> *mut lean_object{
let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); 
v___x_147_ = l_Tree_Zipper_ctorElim___redArg(v_t_144_, v_nodeR_146_);
return v___x_147_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_nodeL_elim___redArg(mut v_t_148_: *mut lean_object, mut v_nodeL_149_: *mut lean_object) -> *mut lean_object{
let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); 
v___x_150_ = l_Tree_Zipper_ctorElim___redArg(v_t_148_, v_nodeL_149_);
return v___x_150_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_nodeL_elim(mut v_motive_151_: *mut lean_object, mut v_t_152_: *mut lean_object, mut v_h_153_: *mut lean_object, mut v_nodeL_154_: *mut lean_object) -> *mut lean_object{
let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); 
v___x_155_ = l_Tree_Zipper_ctorElim___redArg(v_t_152_, v_nodeL_154_);
return v___x_155_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_done_elim___redArg(mut v_t_156_: *mut lean_object, mut v_done_157_: *mut lean_object) -> *mut lean_object{
let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); 
v___x_158_ = l_Tree_Zipper_ctorElim___redArg(v_t_156_, v_done_157_);
return v___x_158_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_Zipper_done_elim(mut v_motive_159_: *mut lean_object, mut v_t_160_: *mut lean_object, mut v_h_161_: *mut lean_object, mut v_done_162_: *mut lean_object) -> *mut lean_object{
let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); 
v___x_163_ = l_Tree_Zipper_ctorElim___redArg(v_t_160_, v_done_162_);
return v___x_163_;
}
#[no_mangle] pub unsafe extern "C" fn l_rebuild(mut v_t_164_: *mut lean_object, mut v_x_165_: *mut lean_object) -> *mut lean_object{
let mut v_a_166_: u8 = 0; let mut v_a_167_: *mut lean_object = core::ptr::null_mut(); let mut v_a_168_: *mut lean_object = core::ptr::null_mut(); let mut v_a_169_: u8 = 0; let mut v_a_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_172_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_173_: u8 = 0; let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_177_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_178_: u8 = 0; let mut v_a_179_: u8 = 0; let mut v_a_180_: *mut lean_object = core::ptr::null_mut(); let mut v_a_181_: *mut lean_object = core::ptr::null_mut(); let mut v_a_182_: u8 = 0; let mut v_a_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_186_: u8 = 0; let mut v___x_188_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_190_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_191_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_165_)
{
0 => {
let mut v_a_166_: u8 = 0; let mut v_a_167_: *mut lean_object = core::ptr::null_mut(); let mut v_a_168_: *mut lean_object = core::ptr::null_mut(); let mut v_a_169_: u8 = 0; let mut v_a_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_172_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_173_: u8 = 0; let mut v_isSharedCheck_178_: u8 = 0; 
v_a_166_ = lean_ctor_get_uint8(v_x_165_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
v_a_167_ = lean_ctor_get(v_x_165_, 0);
v_a_168_ = lean_ctor_get(v_x_165_, 1);
v_a_169_ = lean_ctor_get_uint8(v_x_165_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_170_ = lean_ctor_get(v_x_165_, 2);
v_isSharedCheck_178_ = (!lean_is_exclusive(v_x_165_)) as u8;
if v_isSharedCheck_178_ == 0 {
v___x_172_ = v_x_165_;
v_isShared_173_ = v_isSharedCheck_178_;
state = 1; continue;
} else {
lean_inc(v_a_170_);
lean_inc(v_a_168_);
lean_inc(v_a_167_);
lean_dec(v_x_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_178_;
state = 1; continue;
}
}
1 => {
let mut v_a_179_: u8 = 0; let mut v_a_180_: *mut lean_object = core::ptr::null_mut(); let mut v_a_181_: *mut lean_object = core::ptr::null_mut(); let mut v_a_182_: u8 = 0; let mut v_a_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_186_: u8 = 0; let mut v_isSharedCheck_191_: u8 = 0; 
v_a_179_ = lean_ctor_get_uint8(v_x_165_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
v_a_180_ = lean_ctor_get(v_x_165_, 0);
v_a_181_ = lean_ctor_get(v_x_165_, 1);
v_a_182_ = lean_ctor_get_uint8(v_x_165_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_183_ = lean_ctor_get(v_x_165_, 2);
v_isSharedCheck_191_ = (!lean_is_exclusive(v_x_165_)) as u8;
if v_isSharedCheck_191_ == 0 {
v___x_185_ = v_x_165_;
v_isShared_186_ = v_isSharedCheck_191_;
state = 3; continue;
} else {
lean_inc(v_a_183_);
lean_inc(v_a_181_);
lean_inc(v_a_180_);
lean_dec(v_x_165_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
state = 3; continue;
}
}
_ => {
return v_t_164_;
}
}
}
1 => {
if v_isShared_173_ == 0 {
lean_ctor_set_tag(v___x_172_, 1);
lean_ctor_set(v___x_172_, 2, v_t_164_);
v___x_175_ = v___x_172_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_177_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_167_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_a_168_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_t_164_);
lean_ctor_set_uint8(v_reuseFailAlloc_177_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_166_);
lean_ctor_set_uint8(v_reuseFailAlloc_177_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_169_);
v___x_175_ = v_reuseFailAlloc_177_;
state = 2; continue;
}
}
3 => {
if v_isShared_186_ == 0 {
lean_ctor_set(v___x_185_, 0, v_t_164_);
v___x_188_ = v___x_185_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_190_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_t_164_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_a_181_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_a_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_179_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_182_);
v___x_188_ = v_reuseFailAlloc_190_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_balance(mut v_l_192_: *mut lean_object, mut v_k_193_: *mut lean_object, mut v_v_194_: u8, mut v_r_195_: *mut lean_object, mut v_x_196_: *mut lean_object) -> *mut lean_object{
let mut v_a_197_: u8 = 0; let mut v_a_198_: *mut lean_object = core::ptr::null_mut(); let mut v_a_199_: *mut lean_object = core::ptr::null_mut(); let mut v_a_200_: *mut lean_object = core::ptr::null_mut(); let mut v_a_201_: u8 = 0; let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_204_: u8 = 0; let mut v_a_205_: *mut lean_object = core::ptr::null_mut(); let mut v_a_206_: *mut lean_object = core::ptr::null_mut(); let mut v_a_207_: u8 = 0; let mut v_a_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_211_: u8 = 0; let mut v___x_212_: u8 = 0; let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_218_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_219_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_220_: u8 = 0; let mut v_isSharedCheck_221_: u8 = 0; let mut v_unused_222_: *mut lean_object = core::ptr::null_mut(); let mut v_a_223_: *mut lean_object = core::ptr::null_mut(); let mut v_a_224_: *mut lean_object = core::ptr::null_mut(); let mut v_a_225_: u8 = 0; let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_228_: u8 = 0; let mut v_a_229_: *mut lean_object = core::ptr::null_mut(); let mut v_a_230_: *mut lean_object = core::ptr::null_mut(); let mut v_a_231_: u8 = 0; let mut v_a_232_: *mut lean_object = core::ptr::null_mut(); let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_235_: u8 = 0; let mut v___x_236_: u8 = 0; let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v___x_240_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_242_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_243_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_244_: u8 = 0; let mut v_isSharedCheck_245_: u8 = 0; let mut v_unused_246_: *mut lean_object = core::ptr::null_mut(); let mut v_a_247_: *mut lean_object = core::ptr::null_mut(); let mut v_a_248_: *mut lean_object = core::ptr::null_mut(); let mut v_a_249_: u8 = 0; let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_252_: u8 = 0; let mut v___x_253_: u8 = 0; let mut v___x_255_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_257_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_258_: u8 = 0; let mut v_unused_259_: *mut lean_object = core::ptr::null_mut(); let mut v_a_260_: *mut lean_object = core::ptr::null_mut(); let mut v_a_261_: *mut lean_object = core::ptr::null_mut(); let mut v_a_262_: u8 = 0; let mut v_a_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_266_: u8 = 0; let mut v___x_267_: u8 = 0; let mut v___x_269_: *mut lean_object = core::ptr::null_mut(); let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_272_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_273_: u8 = 0; let mut v_a_274_: u8 = 0; let mut v_a_275_: *mut lean_object = core::ptr::null_mut(); let mut v_a_276_: *mut lean_object = core::ptr::null_mut(); let mut v_a_277_: u8 = 0; let mut v_a_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_281_: u8 = 0; let mut v_a_282_: *mut lean_object = core::ptr::null_mut(); let mut v_a_283_: *mut lean_object = core::ptr::null_mut(); let mut v_a_284_: u8 = 0; let mut v_a_285_: *mut lean_object = core::ptr::null_mut(); let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_288_: u8 = 0; let mut v___x_289_: u8 = 0; let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_295_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_296_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_297_: u8 = 0; let mut v_isSharedCheck_298_: u8 = 0; let mut v_unused_299_: *mut lean_object = core::ptr::null_mut(); let mut v_a_300_: *mut lean_object = core::ptr::null_mut(); let mut v_a_301_: u8 = 0; let mut v_a_302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_305_: u8 = 0; let mut v_a_306_: *mut lean_object = core::ptr::null_mut(); let mut v_a_307_: *mut lean_object = core::ptr::null_mut(); let mut v_a_308_: u8 = 0; let mut v_a_309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_312_: u8 = 0; let mut v___x_313_: u8 = 0; let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_319_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_320_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_321_: u8 = 0; let mut v_isSharedCheck_322_: u8 = 0; let mut v_unused_323_: *mut lean_object = core::ptr::null_mut(); let mut v_a_324_: *mut lean_object = core::ptr::null_mut(); let mut v_a_325_: u8 = 0; let mut v_a_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_329_: u8 = 0; let mut v___x_330_: u8 = 0; let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_334_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_335_: u8 = 0; let mut v_unused_336_: *mut lean_object = core::ptr::null_mut(); let mut v_a_337_: *mut lean_object = core::ptr::null_mut(); let mut v_a_338_: *mut lean_object = core::ptr::null_mut(); let mut v_a_339_: u8 = 0; let mut v_a_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_343_: u8 = 0; let mut v___x_344_: u8 = 0; let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_349_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_350_: u8 = 0; let mut v___x_351_: u8 = 0; let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_196_)
{
0 => {
let mut v_a_197_: u8 = 0; 
v_a_197_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_197_ == 0 {
let mut v_a_198_: *mut lean_object = core::ptr::null_mut(); 
v_a_198_ = lean_ctor_get(v_x_196_, 2);
lean_inc(v_a_198_);
match lean_obj_tag(v_a_198_)
{
0 => {
let mut v_a_199_: *mut lean_object = core::ptr::null_mut(); let mut v_a_200_: *mut lean_object = core::ptr::null_mut(); let mut v_a_201_: u8 = 0; let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_204_: u8 = 0; let mut v_isSharedCheck_221_: u8 = 0; 
v_a_199_ = lean_ctor_get(v_x_196_, 0);
v_a_200_ = lean_ctor_get(v_x_196_, 1);
v_a_201_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_isSharedCheck_221_ = (!lean_is_exclusive(v_x_196_)) as u8;
if v_isSharedCheck_221_ == 0 {
let mut v_unused_222_: *mut lean_object = core::ptr::null_mut(); 
v_unused_222_ = lean_ctor_get(v_x_196_, 2);
lean_dec(v_unused_222_);
v___x_203_ = v_x_196_;
v_isShared_204_ = v_isSharedCheck_221_;
state = 1; continue;
} else {
lean_inc(v_a_200_);
lean_inc(v_a_199_);
lean_dec(v_x_196_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_221_;
state = 1; continue;
}
}
1 => {
let mut v_a_223_: *mut lean_object = core::ptr::null_mut(); let mut v_a_224_: *mut lean_object = core::ptr::null_mut(); let mut v_a_225_: u8 = 0; let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_228_: u8 = 0; let mut v_isSharedCheck_245_: u8 = 0; 
v_a_223_ = lean_ctor_get(v_x_196_, 0);
v_a_224_ = lean_ctor_get(v_x_196_, 1);
v_a_225_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_isSharedCheck_245_ = (!lean_is_exclusive(v_x_196_)) as u8;
if v_isSharedCheck_245_ == 0 {
let mut v_unused_246_: *mut lean_object = core::ptr::null_mut(); 
v_unused_246_ = lean_ctor_get(v_x_196_, 2);
lean_dec(v_unused_246_);
v___x_227_ = v_x_196_;
v_isShared_228_ = v_isSharedCheck_245_;
state = 5; continue;
} else {
lean_inc(v_a_224_);
lean_inc(v_a_223_);
lean_dec(v_x_196_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_245_;
state = 5; continue;
}
}
_ => {
let mut v_a_247_: *mut lean_object = core::ptr::null_mut(); let mut v_a_248_: *mut lean_object = core::ptr::null_mut(); let mut v_a_249_: u8 = 0; let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_252_: u8 = 0; let mut v_isSharedCheck_258_: u8 = 0; 
v_a_247_ = lean_ctor_get(v_x_196_, 0);
v_a_248_ = lean_ctor_get(v_x_196_, 1);
v_a_249_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_isSharedCheck_258_ = (!lean_is_exclusive(v_x_196_)) as u8;
if v_isSharedCheck_258_ == 0 {
let mut v_unused_259_: *mut lean_object = core::ptr::null_mut(); 
v_unused_259_ = lean_ctor_get(v_x_196_, 2);
lean_dec(v_unused_259_);
v___x_251_ = v_x_196_;
v_isShared_252_ = v_isSharedCheck_258_;
state = 9; continue;
} else {
lean_inc(v_a_248_);
lean_inc(v_a_247_);
lean_dec(v_x_196_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_258_;
state = 9; continue;
}
}
}
} else {
let mut v_a_260_: *mut lean_object = core::ptr::null_mut(); let mut v_a_261_: *mut lean_object = core::ptr::null_mut(); let mut v_a_262_: u8 = 0; let mut v_a_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_266_: u8 = 0; let mut v_isSharedCheck_273_: u8 = 0; 
v_a_260_ = lean_ctor_get(v_x_196_, 0);
v_a_261_ = lean_ctor_get(v_x_196_, 1);
v_a_262_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_263_ = lean_ctor_get(v_x_196_, 2);
v_isSharedCheck_273_ = (!lean_is_exclusive(v_x_196_)) as u8;
if v_isSharedCheck_273_ == 0 {
v___x_265_ = v_x_196_;
v_isShared_266_ = v_isSharedCheck_273_;
state = 11; continue;
} else {
lean_inc(v_a_263_);
lean_inc(v_a_261_);
lean_inc(v_a_260_);
lean_dec(v_x_196_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
state = 11; continue;
}
}
}
1 => {
let mut v_a_274_: u8 = 0; 
v_a_274_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_274_ == 0 {
let mut v_a_275_: *mut lean_object = core::ptr::null_mut(); 
v_a_275_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_a_275_);
match lean_obj_tag(v_a_275_)
{
0 => {
let mut v_a_276_: *mut lean_object = core::ptr::null_mut(); let mut v_a_277_: u8 = 0; let mut v_a_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_281_: u8 = 0; let mut v_isSharedCheck_298_: u8 = 0; 
v_a_276_ = lean_ctor_get(v_x_196_, 1);
v_a_277_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_278_ = lean_ctor_get(v_x_196_, 2);
v_isSharedCheck_298_ = (!lean_is_exclusive(v_x_196_)) as u8;
if v_isSharedCheck_298_ == 0 {
let mut v_unused_299_: *mut lean_object = core::ptr::null_mut(); 
v_unused_299_ = lean_ctor_get(v_x_196_, 0);
lean_dec(v_unused_299_);
v___x_280_ = v_x_196_;
v_isShared_281_ = v_isSharedCheck_298_;
state = 13; continue;
} else {
lean_inc(v_a_278_);
lean_inc(v_a_276_);
lean_dec(v_x_196_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_298_;
state = 13; continue;
}
}
1 => {
let mut v_a_300_: *mut lean_object = core::ptr::null_mut(); let mut v_a_301_: u8 = 0; let mut v_a_302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_305_: u8 = 0; let mut v_isSharedCheck_322_: u8 = 0; 
v_a_300_ = lean_ctor_get(v_x_196_, 1);
v_a_301_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_302_ = lean_ctor_get(v_x_196_, 2);
v_isSharedCheck_322_ = (!lean_is_exclusive(v_x_196_)) as u8;
if v_isSharedCheck_322_ == 0 {
let mut v_unused_323_: *mut lean_object = core::ptr::null_mut(); 
v_unused_323_ = lean_ctor_get(v_x_196_, 0);
lean_dec(v_unused_323_);
v___x_304_ = v_x_196_;
v_isShared_305_ = v_isSharedCheck_322_;
state = 17; continue;
} else {
lean_inc(v_a_302_);
lean_inc(v_a_300_);
lean_dec(v_x_196_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_322_;
state = 17; continue;
}
}
_ => {
let mut v_a_324_: *mut lean_object = core::ptr::null_mut(); let mut v_a_325_: u8 = 0; let mut v_a_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_329_: u8 = 0; let mut v_isSharedCheck_335_: u8 = 0; 
v_a_324_ = lean_ctor_get(v_x_196_, 1);
v_a_325_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_326_ = lean_ctor_get(v_x_196_, 2);
v_isSharedCheck_335_ = (!lean_is_exclusive(v_x_196_)) as u8;
if v_isSharedCheck_335_ == 0 {
let mut v_unused_336_: *mut lean_object = core::ptr::null_mut(); 
v_unused_336_ = lean_ctor_get(v_x_196_, 0);
lean_dec(v_unused_336_);
v___x_328_ = v_x_196_;
v_isShared_329_ = v_isSharedCheck_335_;
state = 21; continue;
} else {
lean_inc(v_a_326_);
lean_inc(v_a_324_);
lean_dec(v_x_196_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_335_;
state = 21; continue;
}
}
}
} else {
let mut v_a_337_: *mut lean_object = core::ptr::null_mut(); let mut v_a_338_: *mut lean_object = core::ptr::null_mut(); let mut v_a_339_: u8 = 0; let mut v_a_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_343_: u8 = 0; let mut v_isSharedCheck_350_: u8 = 0; 
v_a_337_ = lean_ctor_get(v_x_196_, 0);
v_a_338_ = lean_ctor_get(v_x_196_, 1);
v_a_339_ = lean_ctor_get_uint8(v_x_196_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_340_ = lean_ctor_get(v_x_196_, 2);
v_isSharedCheck_350_ = (!lean_is_exclusive(v_x_196_)) as u8;
if v_isSharedCheck_350_ == 0 {
v___x_342_ = v_x_196_;
v_isShared_343_ = v_isSharedCheck_350_;
state = 23; continue;
} else {
lean_inc(v_a_340_);
lean_inc(v_a_338_);
lean_inc(v_a_337_);
lean_dec(v_x_196_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_350_;
state = 23; continue;
}
}
}
_ => {
let mut v___x_351_: u8 = 0; let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); 
v___x_351_ = 1;
v___x_352_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_352_, 0, v_l_192_);
lean_ctor_set(v___x_352_, 1, v_k_193_);
lean_ctor_set(v___x_352_, 2, v_r_195_);
lean_ctor_set_uint8(v___x_352_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_351_);
lean_ctor_set_uint8(v___x_352_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_v_194_);
return v___x_352_;
}
}
}
1 => {
v_a_205_ = lean_ctor_get(v_a_198_, 0);
v_a_206_ = lean_ctor_get(v_a_198_, 1);
v_a_207_ = lean_ctor_get_uint8(v_a_198_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_208_ = lean_ctor_get(v_a_198_, 2);
v_isSharedCheck_220_ = (!lean_is_exclusive(v_a_198_)) as u8;
if v_isSharedCheck_220_ == 0 {
v___x_210_ = v_a_198_;
v_isShared_211_ = v_isSharedCheck_220_;
state = 2; continue;
} else {
lean_inc(v_a_208_);
lean_inc(v_a_206_);
lean_inc(v_a_205_);
lean_dec(v_a_198_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_220_;
state = 2; continue;
}
}
5 => {
v_a_229_ = lean_ctor_get(v_a_198_, 0);
v_a_230_ = lean_ctor_get(v_a_198_, 1);
v_a_231_ = lean_ctor_get_uint8(v_a_198_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_232_ = lean_ctor_get(v_a_198_, 2);
v_isSharedCheck_244_ = (!lean_is_exclusive(v_a_198_)) as u8;
if v_isSharedCheck_244_ == 0 {
v___x_234_ = v_a_198_;
v_isShared_235_ = v_isSharedCheck_244_;
state = 6; continue;
} else {
lean_inc(v_a_232_);
lean_inc(v_a_230_);
lean_inc(v_a_229_);
lean_dec(v_a_198_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_244_;
state = 6; continue;
}
}
9 => {
v___x_253_ = 1;
if v_isShared_252_ == 0 {
lean_ctor_set_tag(v___x_251_, 1);
lean_ctor_set(v___x_251_, 2, v_r_195_);
lean_ctor_set(v___x_251_, 1, v_k_193_);
lean_ctor_set(v___x_251_, 0, v_l_192_);
v___x_255_ = v___x_251_;
state = 10; continue;
} else {
let mut v_reuseFailAlloc_257_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_l_192_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_k_193_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_r_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_257_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_197_);
v___x_255_ = v_reuseFailAlloc_257_;
state = 10; continue;
}
}
11 => {
v___x_267_ = 0;
if v_isShared_266_ == 0 {
lean_ctor_set_tag(v___x_265_, 1);
lean_ctor_set(v___x_265_, 2, v_r_195_);
lean_ctor_set(v___x_265_, 1, v_k_193_);
lean_ctor_set(v___x_265_, 0, v_l_192_);
v___x_269_ = v___x_265_;
state = 12; continue;
} else {
let mut v_reuseFailAlloc_272_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_l_192_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_k_193_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_r_195_);
v___x_269_ = v_reuseFailAlloc_272_;
state = 12; continue;
}
}
13 => {
v_a_282_ = lean_ctor_get(v_a_275_, 0);
v_a_283_ = lean_ctor_get(v_a_275_, 1);
v_a_284_ = lean_ctor_get_uint8(v_a_275_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_285_ = lean_ctor_get(v_a_275_, 2);
v_isSharedCheck_297_ = (!lean_is_exclusive(v_a_275_)) as u8;
if v_isSharedCheck_297_ == 0 {
v___x_287_ = v_a_275_;
v_isShared_288_ = v_isSharedCheck_297_;
state = 14; continue;
} else {
lean_inc(v_a_285_);
lean_inc(v_a_283_);
lean_inc(v_a_282_);
lean_dec(v_a_275_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_297_;
state = 14; continue;
}
}
17 => {
v_a_306_ = lean_ctor_get(v_a_275_, 0);
v_a_307_ = lean_ctor_get(v_a_275_, 1);
v_a_308_ = lean_ctor_get_uint8(v_a_275_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_309_ = lean_ctor_get(v_a_275_, 2);
v_isSharedCheck_321_ = (!lean_is_exclusive(v_a_275_)) as u8;
if v_isSharedCheck_321_ == 0 {
v___x_311_ = v_a_275_;
v_isShared_312_ = v_isSharedCheck_321_;
state = 18; continue;
} else {
lean_inc(v_a_309_);
lean_inc(v_a_307_);
lean_inc(v_a_306_);
lean_dec(v_a_275_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_321_;
state = 18; continue;
}
}
21 => {
v___x_330_ = 1;
if v_isShared_329_ == 0 {
lean_ctor_set(v___x_328_, 2, v_r_195_);
lean_ctor_set(v___x_328_, 1, v_k_193_);
lean_ctor_set(v___x_328_, 0, v_l_192_);
v___x_332_ = v___x_328_;
state = 22; continue;
} else {
let mut v_reuseFailAlloc_334_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_l_192_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_k_193_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_r_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_334_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_274_);
v___x_332_ = v_reuseFailAlloc_334_;
state = 22; continue;
}
}
23 => {
v___x_344_ = 0;
if v_isShared_343_ == 0 {
lean_ctor_set(v___x_342_, 2, v_r_195_);
lean_ctor_set(v___x_342_, 1, v_k_193_);
lean_ctor_set(v___x_342_, 0, v_l_192_);
v___x_346_ = v___x_342_;
state = 24; continue;
} else {
let mut v_reuseFailAlloc_349_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_l_192_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_k_193_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_r_195_);
v___x_346_ = v_reuseFailAlloc_349_;
state = 24; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_balance___boxed(mut v_l_353_: *mut lean_object, mut v_k_354_: *mut lean_object, mut v_v_355_: *mut lean_object, mut v_r_356_: *mut lean_object, mut v_x_357_: *mut lean_object) -> *mut lean_object{
let mut v_v_boxed_358_: u8 = 0; let mut v_res_359_: *mut lean_object = core::ptr::null_mut(); 
v_v_boxed_358_ = (lean_unbox(v_v_355_) as u8);
v_res_359_ = l_balance(v_l_353_, v_k_354_, v_v_boxed_358_, v_r_356_, v_x_357_);
return v_res_359_;
}
#[no_mangle] pub unsafe extern "C" fn l_ins(mut v_kx_360_: *mut lean_object, mut v_vx_361_: u8, mut v_z_362_: *mut lean_object, mut v_x_363_: *mut lean_object) -> *mut lean_object{
let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); let mut v_a_365_: u8 = 0; let mut v_a_366_: *mut lean_object = core::ptr::null_mut(); let mut v_a_367_: *mut lean_object = core::ptr::null_mut(); let mut v_a_368_: u8 = 0; let mut v_a_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_372_: u8 = 0; let mut v___x_373_: u8 = 0; let mut v___x_374_: u8 = 0; let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_383_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_363_) == 0 {
let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); 
v___x_364_ = l_balance(v_x_363_, v_kx_360_, v_vx_361_, v_x_363_, v_z_362_);
return v___x_364_;
} else {
let mut v_a_365_: u8 = 0; let mut v_a_366_: *mut lean_object = core::ptr::null_mut(); let mut v_a_367_: *mut lean_object = core::ptr::null_mut(); let mut v_a_368_: u8 = 0; let mut v_a_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_372_: u8 = 0; let mut v_isSharedCheck_383_: u8 = 0; 
v_a_365_ = lean_ctor_get_uint8(v_x_363_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
v_a_366_ = lean_ctor_get(v_x_363_, 0);
v_a_367_ = lean_ctor_get(v_x_363_, 1);
v_a_368_ = lean_ctor_get_uint8(v_x_363_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_369_ = lean_ctor_get(v_x_363_, 2);
v_isSharedCheck_383_ = (!lean_is_exclusive(v_x_363_)) as u8;
if v_isSharedCheck_383_ == 0 {
v___x_371_ = v_x_363_;
v_isShared_372_ = v_isSharedCheck_383_;
state = 1; continue;
} else {
lean_inc(v_a_369_);
lean_inc(v_a_367_);
lean_inc(v_a_366_);
lean_dec(v_x_363_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_383_;
state = 1; continue;
}
}
}
1 => {
v___x_373_ = lean_nat_dec_lt(v_kx_360_, v_a_367_);
if v___x_373_ == 0 {
let mut v___x_374_: u8 = 0; 
v___x_374_ = lean_nat_dec_lt(v_a_367_, v_kx_360_);
if v___x_374_ == 0 {
let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_367_);
if v_isShared_372_ == 0 {
lean_ctor_set(v___x_371_, 1, v_kx_360_);
v___x_376_ = v___x_371_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_378_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_366_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_kx_360_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_a_369_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_365_);
v___x_376_ = v_reuseFailAlloc_378_;
state = 2; continue;
}
} else {
let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_371_);
v___x_379_ = lean_alloc_ctor(0, 3, (2) as u32);
lean_ctor_set(v___x_379_, 0, v_a_366_);
lean_ctor_set(v___x_379_, 1, v_a_367_);
lean_ctor_set(v___x_379_, 2, v_z_362_);
lean_ctor_set_uint8(v___x_379_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_365_);
lean_ctor_set_uint8(v___x_379_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_368_);
v_z_362_ = v___x_379_;
v_x_363_ = v_a_369_;
state = 0; continue;
}
} else {
let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_371_);
v___x_381_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_381_, 0, v_z_362_);
lean_ctor_set(v___x_381_, 1, v_a_367_);
lean_ctor_set(v___x_381_, 2, v_a_369_);
lean_ctor_set_uint8(v___x_381_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_365_);
lean_ctor_set_uint8(v___x_381_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_368_);
v_z_362_ = v___x_381_;
v_x_363_ = v_a_366_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ins___boxed(mut v_kx_384_: *mut lean_object, mut v_vx_385_: *mut lean_object, mut v_z_386_: *mut lean_object, mut v_x_387_: *mut lean_object) -> *mut lean_object{
let mut v_vx_boxed_388_: u8 = 0; let mut v_res_389_: *mut lean_object = core::ptr::null_mut(); 
v_vx_boxed_388_ = (lean_unbox(v_vx_385_) as u8);
v_res_389_ = l_ins(v_kx_384_, v_vx_boxed_388_, v_z_386_, v_x_387_);
return v_res_389_;
}
#[no_mangle] pub unsafe extern "C" fn l_insert(mut v_k_390_: *mut lean_object, mut v_v_391_: u8, mut v_t_392_: *mut lean_object) -> *mut lean_object{
let mut v___x_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); 
v___x_393_ = lean_box(2);
v___x_394_ = l_ins(v_k_390_, v_v_391_, v___x_393_, v_t_392_);
return v___x_394_;
}
#[no_mangle] pub unsafe extern "C" fn l_insert___boxed(mut v_k_395_: *mut lean_object, mut v_v_396_: *mut lean_object, mut v_t_397_: *mut lean_object) -> *mut lean_object{
let mut v_v_boxed_398_: u8 = 0; let mut v_res_399_: *mut lean_object = core::ptr::null_mut(); 
v_v_boxed_398_ = (lean_unbox(v_v_396_) as u8);
v_res_399_ = l_insert(v_k_395_, v_v_boxed_398_, v_t_397_);
return v_res_399_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkMapAux(mut v_x_400_: *mut lean_object, mut v_x_401_: *mut lean_object) -> *mut lean_object{
let mut v_zero_402_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_403_: u8 = 0; let mut v_one_404_: *mut lean_object = core::ptr::null_mut(); let mut v_n_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: u8 = 0; let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_402_ = lean_unsigned_to_nat(0);
v_isZero_403_ = lean_nat_dec_eq(v_x_400_, v_zero_402_);
if v_isZero_403_ == 1 {
lean_dec(v_x_400_);
return v_x_401_;
} else {
let mut v_one_404_: *mut lean_object = core::ptr::null_mut(); let mut v_n_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: u8 = 0; let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); 
v_one_404_ = lean_unsigned_to_nat(1);
v_n_405_ = lean_nat_sub(v_x_400_, v_one_404_);
lean_dec(v_x_400_);
v___x_406_ = lean_unsigned_to_nat(10);
v___x_407_ = lean_nat_mod(v_n_405_, v___x_406_);
v___x_408_ = lean_nat_dec_eq(v___x_407_, v_zero_402_);
lean_dec(v___x_407_);
lean_inc(v_n_405_);
v___x_409_ = l_insert(v_n_405_, v___x_408_, v_x_401_);
v_x_400_ = v_n_405_;
v_x_401_ = v___x_409_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mkMap(mut v_n_411_: *mut lean_object) -> *mut lean_object{
let mut v___x_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_413_: *mut lean_object = core::ptr::null_mut(); 
v___x_412_ = lean_box(0);
v___x_413_ = l_mkMapAux(v_n_411_, v___x_412_);
return v___x_413_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v_x_414_: *mut lean_object, mut v_v_415_: u8, mut v_r_416_: *mut lean_object) -> *mut lean_object{
if v_v_415_ == 0 {
lean_inc(v_r_416_);
return v_r_416_;
} else {
let mut v___x_417_: *mut lean_object = core::ptr::null_mut(); let mut v___x_418_: *mut lean_object = core::ptr::null_mut(); 
v___x_417_ = lean_unsigned_to_nat(1);
v___x_418_ = lean_nat_add(v_r_416_, v___x_417_);
return v___x_418_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0___boxed(mut v_x_419_: *mut lean_object, mut v_v_420_: *mut lean_object, mut v_r_421_: *mut lean_object) -> *mut lean_object{
let mut v_v_boxed_422_: u8 = 0; let mut v_res_423_: *mut lean_object = core::ptr::null_mut(); 
v_v_boxed_422_ = (lean_unbox(v_v_420_) as u8);
v_res_423_ = l_main___lam__0(v_x_419_, v_v_boxed_422_, v_r_421_);
lean_dec(v_r_421_);
lean_dec(v_x_419_);
return v_res_423_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_424_: *mut lean_object) -> *mut lean_object{
let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); 
v___x_426_ = lean_get_stdout();
v_putStr_427_ = lean_ctor_get(v___x_426_, 4);
lean_inc_ref(v_putStr_427_);
lean_dec_ref(v___x_426_);
v___x_428_ = lean_apply_2(v_putStr_427_, v_s_424_, lean_box(0));
return v___x_428_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_429_: *mut lean_object, mut v_a_430_: *mut lean_object) -> *mut lean_object{
let mut v_res_431_: *mut lean_object = core::ptr::null_mut(); 
v_res_431_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_429_);
return v_res_431_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_432_: *mut lean_object) -> *mut lean_object{
let mut v___x_434_: u32 = 0; let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_436_: *mut lean_object = core::ptr::null_mut(); 
v___x_434_ = 10;
v___x_435_ = lean_string_push(v_s_432_, v___x_434_);
v___x_436_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_435_);
return v___x_436_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_437_: *mut lean_object, mut v_a_438_: *mut lean_object) -> *mut lean_object{
let mut v_res_439_: *mut lean_object = core::ptr::null_mut(); 
v_res_439_ = l_IO_println___at___00main_spec__0(v_s_437_);
return v_res_439_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_442_: *mut lean_object) -> *mut lean_object{
let mut v___f_444_: *mut lean_object = core::ptr::null_mut(); let mut v___x_445_: *mut lean_object = core::ptr::null_mut(); let mut v___x_446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_447_: *mut lean_object = core::ptr::null_mut(); let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); let mut v_m_451_: *mut lean_object = core::ptr::null_mut(); let mut v_v_452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_453_: *mut lean_object = core::ptr::null_mut(); let mut v___x_454_: *mut lean_object = core::ptr::null_mut(); 
v___f_444_ = l_main___closed__0;
v___x_445_ = l_main___closed__1;
v___x_446_ = l_List_head_x21___redArg(v___x_445_, v_xs_442_);
lean_dec(v_xs_442_);
v___x_447_ = lean_unsigned_to_nat(0);
v___x_448_ = lean_string_utf8_byte_size(v___x_446_);
v___x_449_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_449_, 0, v___x_446_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
lean_ctor_set(v___x_449_, 2, v___x_448_);
v___x_450_ = l_String_Slice_toNat_x21(v___x_449_);
lean_dec_ref_known(v___x_449_, 3);
v_m_451_ = l_mkMap(v___x_450_);
v_v_452_ = l_fold___redArg(v___f_444_, v_m_451_, v___x_447_);
v___x_453_ = l_Nat_reprFast(v_v_452_);
v___x_454_ = l_IO_println___at___00main_spec__0(v___x_453_);
return v___x_454_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_455_: *mut lean_object, mut v_a_456_: *mut lean_object) -> *mut lean_object{
let mut v_res_457_: *mut lean_object = core::ptr::null_mut(); 
v_res_457_ = _lean_main(v_xs_455_);
return v_res_457_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_rbmap__fbip(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    let mut args_list = lean_box(0);
            let mut i = argc;
            while i > 1 {
                i -= 1;
                let arg_str = lean_mk_string(*argv.add(i as usize));
                let mut fields = [arg_str, args_list];
                args_list = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(args_list, 0, arg_str);
                lean_ctor_set(args_list, 1, fields[1]);
            }
            return _lean_main(args_list);
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_rbmap__fbip(1 /* builtin */);
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
