// Lean compiler output
// Module: rbmap_checkpoint
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_List_head_x21___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static mut l_instInhabitedTree_default: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_instInhabitedTree: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 105, 110, 112, 117, 116, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 18 }, m_objs: [core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
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
#[no_mangle] pub unsafe extern "C" fn _init_l_instInhabitedTree_default() -> *mut lean_object{
let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); 
v___x_96_ = lean_box(0);
return v___x_96_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_instInhabitedTree() -> *mut lean_object{
let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); 
v___x_97_ = lean_box(0);
return v___x_97_;
}
#[no_mangle] pub unsafe extern "C" fn l_fold___redArg(mut v_f_98_: *mut lean_object, mut v_x_99_: *mut lean_object, mut v_x_100_: *mut lean_object) -> *mut lean_object{
let mut v_a_101_: *mut lean_object = core::ptr::null_mut(); let mut v_a_102_: *mut lean_object = core::ptr::null_mut(); let mut v_a_103_: u8 = 0; let mut v_a_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_99_) == 0 {
lean_dec(v_f_98_);
return v_x_100_;
} else {
let mut v_a_101_: *mut lean_object = core::ptr::null_mut(); let mut v_a_102_: *mut lean_object = core::ptr::null_mut(); let mut v_a_103_: u8 = 0; let mut v_a_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); 
v_a_101_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_a_101_);
v_a_102_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v_a_102_);
v_a_103_ = lean_ctor_get_uint8(v_x_99_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_104_ = lean_ctor_get(v_x_99_, 2);
lean_inc(v_a_104_);
lean_dec_ref_known(v_x_99_, 3);
lean_inc_n(v_f_98_, 2);
v___x_105_ = l_fold___redArg(v_f_98_, v_a_101_, v_x_100_);
v___x_106_ = lean_box((v_a_103_) as usize);
v___x_107_ = lean_apply_3(v_f_98_, v_a_102_, v___x_106_, v___x_105_);
v_x_99_ = v_a_104_;
v_x_100_ = v___x_107_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_fold(mut v_00_u03c3_109_: *mut lean_object, mut v_f_110_: *mut lean_object, mut v_x_111_: *mut lean_object, mut v_x_112_: *mut lean_object) -> *mut lean_object{
let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); 
v___x_113_ = l_fold___redArg(v_f_110_, v_x_111_, v_x_112_);
return v___x_113_;
}
#[no_mangle] pub unsafe extern "C" fn l_balance1(mut v_x_114_: *mut lean_object, mut v_x_115_: u8, mut v_x_116_: *mut lean_object, mut v_x_117_: *mut lean_object) -> *mut lean_object{
let mut v_kv_119_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_120_: u8 = 0; let mut v_t_121_: *mut lean_object = core::ptr::null_mut(); let mut v_l_122_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_123_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_124_: u8 = 0; let mut v_r_u2081_125_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_126_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_127_: u8 = 0; let mut v_r_u2082_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: u8 = 0; let mut v___x_130_: u8 = 0; let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v_a_134_: *mut lean_object = core::ptr::null_mut(); let mut v_a_135_: *mut lean_object = core::ptr::null_mut(); let mut v_a_136_: u8 = 0; let mut v_a_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_140_: u8 = 0; let mut v_kv_142_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_143_: u8 = 0; let mut v_t_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: u8 = 0; let mut v___x_146_: u8 = 0; let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_150_: *mut lean_object = core::ptr::null_mut(); let mut v_a_151_: u8 = 0; let mut v_a_152_: *mut lean_object = core::ptr::null_mut(); let mut v_a_153_: *mut lean_object = core::ptr::null_mut(); let mut v_a_154_: u8 = 0; let mut v_a_155_: *mut lean_object = core::ptr::null_mut(); let mut v_a_156_: u8 = 0; let mut v_a_157_: *mut lean_object = core::ptr::null_mut(); let mut v_a_158_: *mut lean_object = core::ptr::null_mut(); let mut v_a_159_: u8 = 0; let mut v_a_160_: *mut lean_object = core::ptr::null_mut(); let mut v_a_161_: u8 = 0; let mut v_a_162_: *mut lean_object = core::ptr::null_mut(); let mut v_a_163_: *mut lean_object = core::ptr::null_mut(); let mut v_a_164_: u8 = 0; let mut v_a_165_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_166_: u8 = 0; let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_117_) == 1 {
let mut v_a_134_: *mut lean_object = core::ptr::null_mut(); let mut v_a_135_: *mut lean_object = core::ptr::null_mut(); let mut v_a_136_: u8 = 0; let mut v_a_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_140_: u8 = 0; let mut v_isSharedCheck_166_: u8 = 0; 
v_a_134_ = lean_ctor_get(v_x_117_, 0);
v_a_135_ = lean_ctor_get(v_x_117_, 1);
v_a_136_ = lean_ctor_get_uint8(v_x_117_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_137_ = lean_ctor_get(v_x_117_, 2);
v_isSharedCheck_166_ = (!lean_is_exclusive(v_x_117_)) as u8;
if v_isSharedCheck_166_ == 0 {
v___x_139_ = v_x_117_;
v_isShared_140_ = v_isSharedCheck_166_;
state = 2; continue;
} else {
lean_inc(v_a_137_);
lean_inc(v_a_135_);
lean_inc(v_a_134_);
lean_dec(v_x_117_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_166_;
state = 2; continue;
}
} else {
let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_117_);
lean_dec(v_x_116_);
lean_dec(v_x_114_);
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
1 => {
v___x_129_ = 0;
v___x_130_ = 1;
v___x_131_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_131_, 0, v_l_122_);
lean_ctor_set(v___x_131_, 1, v_kx_123_);
lean_ctor_set(v___x_131_, 2, v_r_u2081_125_);
lean_ctor_set_uint8(v___x_131_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_130_);
lean_ctor_set_uint8(v___x_131_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_124_);
v___x_132_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_132_, 0, v_r_u2082_128_);
lean_ctor_set(v___x_132_, 1, v_kv_119_);
lean_ctor_set(v___x_132_, 2, v_t_121_);
lean_ctor_set_uint8(v___x_132_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_130_);
lean_ctor_set_uint8(v___x_132_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vv_120_);
v___x_133_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v_ky_126_);
lean_ctor_set(v___x_133_, 2, v___x_132_);
lean_ctor_set_uint8(v___x_133_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_129_);
lean_ctor_set_uint8(v___x_133_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vy_127_);
return v___x_133_;
}
2 => {
if lean_obj_tag(v_a_134_) == 1 {
let mut v_a_151_: u8 = 0; 
v_a_151_ = lean_ctor_get_uint8(v_a_134_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_151_ == 0 {
let mut v_a_152_: *mut lean_object = core::ptr::null_mut(); let mut v_a_153_: *mut lean_object = core::ptr::null_mut(); let mut v_a_154_: u8 = 0; let mut v_a_155_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_139_);
v_a_152_ = lean_ctor_get(v_a_134_, 0);
lean_inc(v_a_152_);
v_a_153_ = lean_ctor_get(v_a_134_, 1);
lean_inc(v_a_153_);
v_a_154_ = lean_ctor_get_uint8(v_a_134_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_155_ = lean_ctor_get(v_a_134_, 2);
lean_inc(v_a_155_);
lean_dec_ref_known(v_a_134_, 3);
v_kv_119_ = v_x_114_;
v_vv_120_ = v_x_115_;
v_t_121_ = v_x_116_;
v_l_122_ = v_a_152_;
v_kx_123_ = v_a_153_;
v_vx_124_ = v_a_154_;
v_r_u2081_125_ = v_a_155_;
v_ky_126_ = v_a_135_;
v_vy_127_ = v_a_136_;
v_r_u2082_128_ = v_a_137_;
state = 1; continue;
} else {
if lean_obj_tag(v_a_137_) == 1 {
let mut v_a_156_: u8 = 0; 
v_a_156_ = lean_ctor_get_uint8(v_a_137_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_156_ == 0 {
let mut v_a_157_: *mut lean_object = core::ptr::null_mut(); let mut v_a_158_: *mut lean_object = core::ptr::null_mut(); let mut v_a_159_: u8 = 0; let mut v_a_160_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_139_);
v_a_157_ = lean_ctor_get(v_a_137_, 0);
lean_inc(v_a_157_);
v_a_158_ = lean_ctor_get(v_a_137_, 1);
lean_inc(v_a_158_);
v_a_159_ = lean_ctor_get_uint8(v_a_137_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_160_ = lean_ctor_get(v_a_137_, 2);
lean_inc(v_a_160_);
lean_dec_ref_known(v_a_137_, 3);
v_kv_119_ = v_x_114_;
v_vv_120_ = v_x_115_;
v_t_121_ = v_x_116_;
v_l_122_ = v_a_134_;
v_kx_123_ = v_a_135_;
v_vx_124_ = v_a_136_;
v_r_u2081_125_ = v_a_157_;
v_ky_126_ = v_a_158_;
v_vy_127_ = v_a_159_;
v_r_u2082_128_ = v_a_160_;
state = 1; continue;
} else {
v_kv_142_ = v_x_114_;
v_vv_143_ = v_x_115_;
v_t_144_ = v_x_116_;
state = 3; continue;
}
} else {
v_kv_142_ = v_x_114_;
v_vv_143_ = v_x_115_;
v_t_144_ = v_x_116_;
state = 3; continue;
}
}
} else {
if lean_obj_tag(v_a_137_) == 1 {
let mut v_a_161_: u8 = 0; 
v_a_161_ = lean_ctor_get_uint8(v_a_137_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_161_ == 0 {
let mut v_a_162_: *mut lean_object = core::ptr::null_mut(); let mut v_a_163_: *mut lean_object = core::ptr::null_mut(); let mut v_a_164_: u8 = 0; let mut v_a_165_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_139_);
v_a_162_ = lean_ctor_get(v_a_137_, 0);
lean_inc(v_a_162_);
v_a_163_ = lean_ctor_get(v_a_137_, 1);
lean_inc(v_a_163_);
v_a_164_ = lean_ctor_get_uint8(v_a_137_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_165_ = lean_ctor_get(v_a_137_, 2);
lean_inc(v_a_165_);
lean_dec_ref_known(v_a_137_, 3);
v_kv_119_ = v_x_114_;
v_vv_120_ = v_x_115_;
v_t_121_ = v_x_116_;
v_l_122_ = v_a_134_;
v_kx_123_ = v_a_135_;
v_vx_124_ = v_a_136_;
v_r_u2081_125_ = v_a_162_;
v_ky_126_ = v_a_163_;
v_vy_127_ = v_a_164_;
v_r_u2082_128_ = v_a_165_;
state = 1; continue;
} else {
v_kv_142_ = v_x_114_;
v_vv_143_ = v_x_115_;
v_t_144_ = v_x_116_;
state = 3; continue;
}
} else {
v_kv_142_ = v_x_114_;
v_vv_143_ = v_x_115_;
v_t_144_ = v_x_116_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_balance1___boxed(mut v_x_168_: *mut lean_object, mut v_x_169_: *mut lean_object, mut v_x_170_: *mut lean_object, mut v_x_171_: *mut lean_object) -> *mut lean_object{
let mut v_x_136__boxed_172_: u8 = 0; let mut v_res_173_: *mut lean_object = core::ptr::null_mut(); 
v_x_136__boxed_172_ = (lean_unbox(v_x_169_) as u8);
v_res_173_ = l_balance1(v_x_168_, v_x_136__boxed_172_, v_x_170_, v_x_171_);
return v_res_173_;
}
#[no_mangle] pub unsafe extern "C" fn l_balance2(mut v_x_174_: *mut lean_object, mut v_x_175_: *mut lean_object, mut v_x_176_: u8, mut v_x_177_: *mut lean_object) -> *mut lean_object{
let mut v_t_179_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_180_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_181_: u8 = 0; let mut v_l_182_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_u2081_183_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_u2081_184_: u8 = 0; let mut v_r_u2081_185_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_186_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_187_: u8 = 0; let mut v_r_u2082_188_: *mut lean_object = core::ptr::null_mut(); let mut v___x_189_: u8 = 0; let mut v___x_190_: u8 = 0; let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v___x_193_: *mut lean_object = core::ptr::null_mut(); let mut v_a_194_: *mut lean_object = core::ptr::null_mut(); let mut v_a_195_: *mut lean_object = core::ptr::null_mut(); let mut v_a_196_: u8 = 0; let mut v_a_197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_200_: u8 = 0; let mut v_t_202_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_203_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_204_: u8 = 0; let mut v___x_205_: u8 = 0; let mut v___x_206_: u8 = 0; let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_210_: *mut lean_object = core::ptr::null_mut(); let mut v_a_211_: u8 = 0; let mut v_a_212_: *mut lean_object = core::ptr::null_mut(); let mut v_a_213_: *mut lean_object = core::ptr::null_mut(); let mut v_a_214_: u8 = 0; let mut v_a_215_: *mut lean_object = core::ptr::null_mut(); let mut v_a_216_: u8 = 0; let mut v_a_217_: *mut lean_object = core::ptr::null_mut(); let mut v_a_218_: *mut lean_object = core::ptr::null_mut(); let mut v_a_219_: u8 = 0; let mut v_a_220_: *mut lean_object = core::ptr::null_mut(); let mut v_a_221_: u8 = 0; let mut v_a_222_: *mut lean_object = core::ptr::null_mut(); let mut v_a_223_: *mut lean_object = core::ptr::null_mut(); let mut v_a_224_: u8 = 0; let mut v_a_225_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_226_: u8 = 0; let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_177_) == 1 {
let mut v_a_194_: *mut lean_object = core::ptr::null_mut(); let mut v_a_195_: *mut lean_object = core::ptr::null_mut(); let mut v_a_196_: u8 = 0; let mut v_a_197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_200_: u8 = 0; let mut v_isSharedCheck_226_: u8 = 0; 
v_a_194_ = lean_ctor_get(v_x_177_, 0);
v_a_195_ = lean_ctor_get(v_x_177_, 1);
v_a_196_ = lean_ctor_get_uint8(v_x_177_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_197_ = lean_ctor_get(v_x_177_, 2);
v_isSharedCheck_226_ = (!lean_is_exclusive(v_x_177_)) as u8;
if v_isSharedCheck_226_ == 0 {
v___x_199_ = v_x_177_;
v_isShared_200_ = v_isSharedCheck_226_;
state = 2; continue;
} else {
lean_inc(v_a_197_);
lean_inc(v_a_195_);
lean_inc(v_a_194_);
lean_dec(v_x_177_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_226_;
state = 2; continue;
}
} else {
let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_177_);
lean_dec(v_x_175_);
lean_dec(v_x_174_);
v___x_227_ = lean_box(0);
return v___x_227_;
}
}
1 => {
v___x_189_ = 0;
v___x_190_ = 1;
v___x_191_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_191_, 0, v_t_179_);
lean_ctor_set(v___x_191_, 1, v_kv_180_);
lean_ctor_set(v___x_191_, 2, v_l_182_);
lean_ctor_set_uint8(v___x_191_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_190_);
lean_ctor_set_uint8(v___x_191_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vv_181_);
v___x_192_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_192_, 0, v_r_u2081_185_);
lean_ctor_set(v___x_192_, 1, v_ky_186_);
lean_ctor_set(v___x_192_, 2, v_r_u2082_188_);
lean_ctor_set_uint8(v___x_192_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_190_);
lean_ctor_set_uint8(v___x_192_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vy_187_);
v___x_193_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v_kx_u2081_183_);
lean_ctor_set(v___x_193_, 2, v___x_192_);
lean_ctor_set_uint8(v___x_193_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_189_);
lean_ctor_set_uint8(v___x_193_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_u2081_184_);
return v___x_193_;
}
2 => {
if lean_obj_tag(v_a_194_) == 1 {
let mut v_a_211_: u8 = 0; 
v_a_211_ = lean_ctor_get_uint8(v_a_194_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_211_ == 0 {
let mut v_a_212_: *mut lean_object = core::ptr::null_mut(); let mut v_a_213_: *mut lean_object = core::ptr::null_mut(); let mut v_a_214_: u8 = 0; let mut v_a_215_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_199_);
v_a_212_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_a_212_);
v_a_213_ = lean_ctor_get(v_a_194_, 1);
lean_inc(v_a_213_);
v_a_214_ = lean_ctor_get_uint8(v_a_194_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_215_ = lean_ctor_get(v_a_194_, 2);
lean_inc(v_a_215_);
lean_dec_ref_known(v_a_194_, 3);
v_t_179_ = v_x_174_;
v_kv_180_ = v_x_175_;
v_vv_181_ = v_x_176_;
v_l_182_ = v_a_212_;
v_kx_u2081_183_ = v_a_213_;
v_vx_u2081_184_ = v_a_214_;
v_r_u2081_185_ = v_a_215_;
v_ky_186_ = v_a_195_;
v_vy_187_ = v_a_196_;
v_r_u2082_188_ = v_a_197_;
state = 1; continue;
} else {
if lean_obj_tag(v_a_197_) == 1 {
let mut v_a_216_: u8 = 0; 
v_a_216_ = lean_ctor_get_uint8(v_a_197_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_216_ == 0 {
let mut v_a_217_: *mut lean_object = core::ptr::null_mut(); let mut v_a_218_: *mut lean_object = core::ptr::null_mut(); let mut v_a_219_: u8 = 0; let mut v_a_220_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_199_);
v_a_217_ = lean_ctor_get(v_a_197_, 0);
lean_inc(v_a_217_);
v_a_218_ = lean_ctor_get(v_a_197_, 1);
lean_inc(v_a_218_);
v_a_219_ = lean_ctor_get_uint8(v_a_197_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_220_ = lean_ctor_get(v_a_197_, 2);
lean_inc(v_a_220_);
lean_dec_ref_known(v_a_197_, 3);
v_t_179_ = v_x_174_;
v_kv_180_ = v_x_175_;
v_vv_181_ = v_x_176_;
v_l_182_ = v_a_194_;
v_kx_u2081_183_ = v_a_195_;
v_vx_u2081_184_ = v_a_196_;
v_r_u2081_185_ = v_a_217_;
v_ky_186_ = v_a_218_;
v_vy_187_ = v_a_219_;
v_r_u2082_188_ = v_a_220_;
state = 1; continue;
} else {
v_t_202_ = v_x_174_;
v_kv_203_ = v_x_175_;
v_vv_204_ = v_x_176_;
state = 3; continue;
}
} else {
v_t_202_ = v_x_174_;
v_kv_203_ = v_x_175_;
v_vv_204_ = v_x_176_;
state = 3; continue;
}
}
} else {
if lean_obj_tag(v_a_197_) == 1 {
let mut v_a_221_: u8 = 0; 
v_a_221_ = lean_ctor_get_uint8(v_a_197_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_221_ == 0 {
let mut v_a_222_: *mut lean_object = core::ptr::null_mut(); let mut v_a_223_: *mut lean_object = core::ptr::null_mut(); let mut v_a_224_: u8 = 0; let mut v_a_225_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_199_);
v_a_222_ = lean_ctor_get(v_a_197_, 0);
lean_inc(v_a_222_);
v_a_223_ = lean_ctor_get(v_a_197_, 1);
lean_inc(v_a_223_);
v_a_224_ = lean_ctor_get_uint8(v_a_197_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_225_ = lean_ctor_get(v_a_197_, 2);
lean_inc(v_a_225_);
lean_dec_ref_known(v_a_197_, 3);
v_t_179_ = v_x_174_;
v_kv_180_ = v_x_175_;
v_vv_181_ = v_x_176_;
v_l_182_ = v_a_194_;
v_kx_u2081_183_ = v_a_195_;
v_vx_u2081_184_ = v_a_196_;
v_r_u2081_185_ = v_a_222_;
v_ky_186_ = v_a_223_;
v_vy_187_ = v_a_224_;
v_r_u2082_188_ = v_a_225_;
state = 1; continue;
} else {
v_t_202_ = v_x_174_;
v_kv_203_ = v_x_175_;
v_vv_204_ = v_x_176_;
state = 3; continue;
}
} else {
v_t_202_ = v_x_174_;
v_kv_203_ = v_x_175_;
v_vv_204_ = v_x_176_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_balance2___boxed(mut v_x_228_: *mut lean_object, mut v_x_229_: *mut lean_object, mut v_x_230_: *mut lean_object, mut v_x_231_: *mut lean_object) -> *mut lean_object{
let mut v_x_137__boxed_232_: u8 = 0; let mut v_res_233_: *mut lean_object = core::ptr::null_mut(); 
v_x_137__boxed_232_ = (lean_unbox(v_x_230_) as u8);
v_res_233_ = l_balance2(v_x_228_, v_x_229_, v_x_137__boxed_232_, v_x_231_);
return v_res_233_;
}
#[no_mangle] pub unsafe extern "C" fn l_isRed(mut v_x_234_: *mut lean_object) -> u8{
if lean_obj_tag(v_x_234_) == 1 {
let mut v_a_235_: u8 = 0; 
v_a_235_ = lean_ctor_get_uint8(v_x_234_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_235_ == 0 {
let mut v___x_236_: u8 = 0; 
v___x_236_ = 1;
return v___x_236_;
} else {
let mut v___x_237_: u8 = 0; 
v___x_237_ = 0;
return v___x_237_;
}
} else {
let mut v___x_238_: u8 = 0; 
v___x_238_ = 0;
return v___x_238_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_isRed___boxed(mut v_x_239_: *mut lean_object) -> *mut lean_object{
let mut v_res_240_: u8 = 0; let mut v_r_241_: *mut lean_object = core::ptr::null_mut(); 
v_res_240_ = l_isRed(v_x_239_);
lean_dec(v_x_239_);
v_r_241_ = lean_box((v_res_240_) as usize);
return v_r_241_;
}
#[no_mangle] pub unsafe extern "C" fn l_ins(mut v_kx_242_: *mut lean_object, mut v_vx_243_: u8, mut v_x_244_: *mut lean_object) -> *mut lean_object{
let mut v___x_245_: u8 = 0; let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); let mut v_a_247_: u8 = 0; let mut v_a_248_: *mut lean_object = core::ptr::null_mut(); let mut v_a_249_: *mut lean_object = core::ptr::null_mut(); let mut v_a_250_: u8 = 0; let mut v_a_251_: *mut lean_object = core::ptr::null_mut(); let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_254_: u8 = 0; let mut v_t_256_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_257_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_258_: u8 = 0; let mut v_l_259_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_u2081_260_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_u2081_261_: u8 = 0; let mut v_r_u2081_262_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_263_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_264_: u8 = 0; let mut v_r_u2082_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: u8 = 0; let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); let mut v___x_269_: *mut lean_object = core::ptr::null_mut(); let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_271_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_273_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_274_: u8 = 0; let mut v_t_275_: *mut lean_object = core::ptr::null_mut(); let mut v_l_276_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_277_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_278_: u8 = 0; let mut v_r_u2081_279_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_280_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_281_: u8 = 0; let mut v_r_u2082_282_: *mut lean_object = core::ptr::null_mut(); let mut v___x_283_: u8 = 0; let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_285_: *mut lean_object = core::ptr::null_mut(); let mut v___x_286_: *mut lean_object = core::ptr::null_mut(); let mut v___x_287_: u8 = 0; let mut v___x_288_: u8 = 0; let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_294_: u8 = 0; let mut v___x_295_: u8 = 0; let mut v___x_296_: u8 = 0; let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v_a_300_: *mut lean_object = core::ptr::null_mut(); let mut v_a_301_: *mut lean_object = core::ptr::null_mut(); let mut v_a_302_: u8 = 0; let mut v_a_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_306_: u8 = 0; let mut v_t_308_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_309_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_310_: u8 = 0; let mut v___x_311_: u8 = 0; let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); let mut v___x_314_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_315_: *mut lean_object = core::ptr::null_mut(); let mut v_a_316_: u8 = 0; let mut v_a_317_: *mut lean_object = core::ptr::null_mut(); let mut v_a_318_: *mut lean_object = core::ptr::null_mut(); let mut v_a_319_: u8 = 0; let mut v_a_320_: *mut lean_object = core::ptr::null_mut(); let mut v_a_321_: u8 = 0; let mut v_a_322_: *mut lean_object = core::ptr::null_mut(); let mut v_a_323_: *mut lean_object = core::ptr::null_mut(); let mut v_a_324_: u8 = 0; let mut v_a_325_: *mut lean_object = core::ptr::null_mut(); let mut v_a_326_: u8 = 0; let mut v_a_327_: *mut lean_object = core::ptr::null_mut(); let mut v_a_328_: *mut lean_object = core::ptr::null_mut(); let mut v_a_329_: u8 = 0; let mut v_a_330_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_331_: u8 = 0; let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: u8 = 0; let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); let mut v_a_338_: *mut lean_object = core::ptr::null_mut(); let mut v_a_339_: *mut lean_object = core::ptr::null_mut(); let mut v_a_340_: u8 = 0; let mut v_a_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_344_: u8 = 0; let mut v_kv_346_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_347_: u8 = 0; let mut v_t_348_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: u8 = 0; let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_353_: *mut lean_object = core::ptr::null_mut(); let mut v_a_354_: u8 = 0; let mut v_a_355_: *mut lean_object = core::ptr::null_mut(); let mut v_a_356_: *mut lean_object = core::ptr::null_mut(); let mut v_a_357_: u8 = 0; let mut v_a_358_: *mut lean_object = core::ptr::null_mut(); let mut v_a_359_: u8 = 0; let mut v_a_360_: *mut lean_object = core::ptr::null_mut(); let mut v_a_361_: *mut lean_object = core::ptr::null_mut(); let mut v_a_362_: u8 = 0; let mut v_a_363_: *mut lean_object = core::ptr::null_mut(); let mut v_a_364_: u8 = 0; let mut v_a_365_: *mut lean_object = core::ptr::null_mut(); let mut v_a_366_: *mut lean_object = core::ptr::null_mut(); let mut v_a_367_: u8 = 0; let mut v_a_368_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_369_: u8 = 0; let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_371_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_244_) == 0 {
let mut v___x_245_: u8 = 0; let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); 
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_246_, 0, v_x_244_);
lean_ctor_set(v___x_246_, 1, v_kx_242_);
lean_ctor_set(v___x_246_, 2, v_x_244_);
lean_ctor_set_uint8(v___x_246_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_245_);
lean_ctor_set_uint8(v___x_246_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_243_);
return v___x_246_;
} else {
let mut v_a_247_: u8 = 0; let mut v_a_248_: *mut lean_object = core::ptr::null_mut(); let mut v_a_249_: *mut lean_object = core::ptr::null_mut(); let mut v_a_250_: u8 = 0; let mut v_a_251_: *mut lean_object = core::ptr::null_mut(); let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_254_: u8 = 0; let mut v_isSharedCheck_371_: u8 = 0; 
v_a_247_ = lean_ctor_get_uint8(v_x_244_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
v_a_248_ = lean_ctor_get(v_x_244_, 0);
v_a_249_ = lean_ctor_get(v_x_244_, 1);
v_a_250_ = lean_ctor_get_uint8(v_x_244_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_251_ = lean_ctor_get(v_x_244_, 2);
v_isSharedCheck_371_ = (!lean_is_exclusive(v_x_244_)) as u8;
if v_isSharedCheck_371_ == 0 {
v___x_253_ = v_x_244_;
v_isShared_254_ = v_isSharedCheck_371_;
state = 1; continue;
} else {
lean_inc(v_a_251_);
lean_inc(v_a_249_);
lean_inc(v_a_248_);
lean_dec(v_x_244_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_371_;
state = 1; continue;
}
}
}
1 => {
if v_a_247_ == 0 {
let mut v___x_287_: u8 = 0; 
lean_del_object(v___x_253_);
v___x_287_ = lean_nat_dec_lt(v_kx_242_, v_a_249_);
if v___x_287_ == 0 {
let mut v___x_288_: u8 = 0; 
v___x_288_ = lean_nat_dec_eq(v_kx_242_, v_a_249_);
if v___x_288_ == 0 {
let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); 
v___x_289_ = l_ins(v_kx_242_, v_vx_243_, v_a_251_);
v___x_290_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_290_, 0, v_a_248_);
lean_ctor_set(v___x_290_, 1, v_a_249_);
lean_ctor_set(v___x_290_, 2, v___x_289_);
lean_ctor_set_uint8(v___x_290_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_247_);
lean_ctor_set_uint8(v___x_290_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_250_);
return v___x_290_;
} else {
let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_249_);
v___x_291_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_291_, 0, v_a_248_);
lean_ctor_set(v___x_291_, 1, v_kx_242_);
lean_ctor_set(v___x_291_, 2, v_a_251_);
lean_ctor_set_uint8(v___x_291_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_247_);
lean_ctor_set_uint8(v___x_291_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_243_);
return v___x_291_;
}
} else {
let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); 
v___x_292_ = l_ins(v_kx_242_, v_vx_243_, v_a_248_);
v___x_293_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_a_249_);
lean_ctor_set(v___x_293_, 2, v_a_251_);
lean_ctor_set_uint8(v___x_293_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_247_);
lean_ctor_set_uint8(v___x_293_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_250_);
return v___x_293_;
}
} else {
let mut v___x_294_: u8 = 0; 
v___x_294_ = lean_nat_dec_lt(v_kx_242_, v_a_249_);
if v___x_294_ == 0 {
let mut v___x_295_: u8 = 0; 
v___x_295_ = lean_nat_dec_eq(v_kx_242_, v_a_249_);
if v___x_295_ == 0 {
let mut v___x_296_: u8 = 0; 
v___x_296_ = l_isRed(v_a_251_);
if v___x_296_ == 0 {
let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_253_);
v___x_297_ = l_ins(v_kx_242_, v_vx_243_, v_a_251_);
v___x_298_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_298_, 0, v_a_248_);
lean_ctor_set(v___x_298_, 1, v_a_249_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
lean_ctor_set_uint8(v___x_298_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_247_);
lean_ctor_set_uint8(v___x_298_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_250_);
return v___x_298_;
} else {
let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); 
v___x_299_ = l_ins(v_kx_242_, v_vx_243_, v_a_251_);
if lean_obj_tag(v___x_299_) == 1 {
let mut v_a_300_: *mut lean_object = core::ptr::null_mut(); let mut v_a_301_: *mut lean_object = core::ptr::null_mut(); let mut v_a_302_: u8 = 0; let mut v_a_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_306_: u8 = 0; let mut v_isSharedCheck_331_: u8 = 0; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_a_301_ = lean_ctor_get(v___x_299_, 1);
v_a_302_ = lean_ctor_get_uint8(v___x_299_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_303_ = lean_ctor_get(v___x_299_, 2);
v_isSharedCheck_331_ = (!lean_is_exclusive(v___x_299_)) as u8;
if v_isSharedCheck_331_ == 0 {
v___x_305_ = v___x_299_;
v_isShared_306_ = v_isSharedCheck_331_;
state = 5; continue;
} else {
lean_inc(v_a_303_);
lean_inc(v_a_301_);
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_331_;
state = 5; continue;
}
} else {
let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_299_);
lean_del_object(v___x_253_);
lean_dec(v_a_249_);
lean_dec(v_a_248_);
v___x_332_ = lean_box(0);
return v___x_332_;
}
}
} else {
let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_253_);
lean_dec(v_a_249_);
v___x_333_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_333_, 0, v_a_248_);
lean_ctor_set(v___x_333_, 1, v_kx_242_);
lean_ctor_set(v___x_333_, 2, v_a_251_);
lean_ctor_set_uint8(v___x_333_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_247_);
lean_ctor_set_uint8(v___x_333_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_243_);
return v___x_333_;
}
} else {
let mut v___x_334_: u8 = 0; 
lean_del_object(v___x_253_);
v___x_334_ = l_isRed(v_a_248_);
if v___x_334_ == 0 {
let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); 
v___x_335_ = l_ins(v_kx_242_, v_vx_243_, v_a_248_);
v___x_336_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_249_);
lean_ctor_set(v___x_336_, 2, v_a_251_);
lean_ctor_set_uint8(v___x_336_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_247_);
lean_ctor_set_uint8(v___x_336_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_250_);
return v___x_336_;
} else {
let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); 
v___x_337_ = l_ins(v_kx_242_, v_vx_243_, v_a_248_);
if lean_obj_tag(v___x_337_) == 1 {
let mut v_a_338_: *mut lean_object = core::ptr::null_mut(); let mut v_a_339_: *mut lean_object = core::ptr::null_mut(); let mut v_a_340_: u8 = 0; let mut v_a_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_344_: u8 = 0; let mut v_isSharedCheck_369_: u8 = 0; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_a_339_ = lean_ctor_get(v___x_337_, 1);
v_a_340_ = lean_ctor_get_uint8(v___x_337_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_341_ = lean_ctor_get(v___x_337_, 2);
v_isSharedCheck_369_ = (!lean_is_exclusive(v___x_337_)) as u8;
if v_isSharedCheck_369_ == 0 {
v___x_343_ = v___x_337_;
v_isShared_344_ = v_isSharedCheck_369_;
state = 8; continue;
} else {
lean_inc(v_a_341_);
lean_inc(v_a_339_);
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_369_;
state = 8; continue;
}
} else {
let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_337_);
lean_dec(v_a_251_);
lean_dec(v_a_249_);
v___x_370_ = lean_box(0);
return v___x_370_;
}
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ins___boxed(mut v_kx_372_: *mut lean_object, mut v_vx_373_: *mut lean_object, mut v_x_374_: *mut lean_object) -> *mut lean_object{
let mut v_vx_boxed_375_: u8 = 0; let mut v_res_376_: *mut lean_object = core::ptr::null_mut(); 
v_vx_boxed_375_ = (lean_unbox(v_vx_373_) as u8);
v_res_376_ = l_ins(v_kx_372_, v_vx_boxed_375_, v_x_374_);
return v_res_376_;
}
#[no_mangle] pub unsafe extern "C" fn l_setBlack(mut v_x_377_: *mut lean_object) -> *mut lean_object{
let mut v_a_378_: *mut lean_object = core::ptr::null_mut(); let mut v_a_379_: *mut lean_object = core::ptr::null_mut(); let mut v_a_380_: u8 = 0; let mut v_a_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_384_: u8 = 0; let mut v___x_385_: u8 = 0; let mut v___x_387_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_388_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_389_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_377_) == 1 {
let mut v_a_378_: *mut lean_object = core::ptr::null_mut(); let mut v_a_379_: *mut lean_object = core::ptr::null_mut(); let mut v_a_380_: u8 = 0; let mut v_a_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_384_: u8 = 0; let mut v_isSharedCheck_389_: u8 = 0; 
v_a_378_ = lean_ctor_get(v_x_377_, 0);
v_a_379_ = lean_ctor_get(v_x_377_, 1);
v_a_380_ = lean_ctor_get_uint8(v_x_377_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_381_ = lean_ctor_get(v_x_377_, 2);
v_isSharedCheck_389_ = (!lean_is_exclusive(v_x_377_)) as u8;
if v_isSharedCheck_389_ == 0 {
v___x_383_ = v_x_377_;
v_isShared_384_ = v_isSharedCheck_389_;
state = 1; continue;
} else {
lean_inc(v_a_381_);
lean_inc(v_a_379_);
lean_inc(v_a_378_);
lean_dec(v_x_377_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
state = 1; continue;
}
} else {
return v_x_377_;
}
}
1 => {
v___x_385_ = 1;
if v_isShared_384_ == 0 {
v___x_387_ = v___x_383_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_388_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_378_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_a_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_a_381_);
lean_ctor_set_uint8(v_reuseFailAlloc_388_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_380_);
v___x_387_ = v_reuseFailAlloc_388_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_insert(mut v_k_390_: *mut lean_object, mut v_v_391_: u8, mut v_t_392_: *mut lean_object) -> *mut lean_object{
let mut v___x_393_: u8 = 0; 
v___x_393_ = l_isRed(v_t_392_);
if v___x_393_ == 0 {
let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); 
v___x_394_ = l_ins(v_k_390_, v_v_391_, v_t_392_);
return v___x_394_;
} else {
let mut v___x_395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_396_: *mut lean_object = core::ptr::null_mut(); 
v___x_395_ = l_ins(v_k_390_, v_v_391_, v_t_392_);
v___x_396_ = l_setBlack(v___x_395_);
return v___x_396_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_insert___boxed(mut v_k_397_: *mut lean_object, mut v_v_398_: *mut lean_object, mut v_t_399_: *mut lean_object) -> *mut lean_object{
let mut v_v_boxed_400_: u8 = 0; let mut v_res_401_: *mut lean_object = core::ptr::null_mut(); 
v_v_boxed_400_ = (lean_unbox(v_v_398_) as u8);
v_res_401_ = l_insert(v_k_397_, v_v_boxed_400_, v_t_399_);
return v_res_401_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkMapAux(mut v_freq_402_: *mut lean_object, mut v_x_403_: *mut lean_object, mut v_x_404_: *mut lean_object, mut v_x_405_: *mut lean_object) -> *mut lean_object{
let mut v_zero_406_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_407_: u8 = 0; let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); let mut v_one_409_: *mut lean_object = core::ptr::null_mut(); let mut v_n_410_: *mut lean_object = core::ptr::null_mut(); let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); let mut v___x_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_413_: u8 = 0; let mut v_m_414_: *mut lean_object = core::ptr::null_mut(); let mut v___x_415_: *mut lean_object = core::ptr::null_mut(); let mut v___x_416_: u8 = 0; let mut v___x_418_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_406_ = lean_unsigned_to_nat(0);
v_isZero_407_ = lean_nat_dec_eq(v_x_403_, v_zero_406_);
if v_isZero_407_ == 1 {
let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_403_);
v___x_408_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_408_, 0, v_x_404_);
lean_ctor_set(v___x_408_, 1, v_x_405_);
return v___x_408_;
} else {
let mut v_one_409_: *mut lean_object = core::ptr::null_mut(); let mut v_n_410_: *mut lean_object = core::ptr::null_mut(); let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); let mut v___x_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_413_: u8 = 0; let mut v_m_414_: *mut lean_object = core::ptr::null_mut(); let mut v___x_415_: *mut lean_object = core::ptr::null_mut(); let mut v___x_416_: u8 = 0; 
v_one_409_ = lean_unsigned_to_nat(1);
v_n_410_ = lean_nat_sub(v_x_403_, v_one_409_);
lean_dec(v_x_403_);
v___x_411_ = lean_unsigned_to_nat(10);
v___x_412_ = lean_nat_mod(v_n_410_, v___x_411_);
v___x_413_ = lean_nat_dec_eq(v___x_412_, v_zero_406_);
lean_dec(v___x_412_);
lean_inc(v_n_410_);
v_m_414_ = l_insert(v_n_410_, v___x_413_, v_x_404_);
v___x_415_ = lean_nat_mod(v_n_410_, v_freq_402_);
v___x_416_ = lean_nat_dec_eq(v___x_415_, v_zero_406_);
lean_dec(v___x_415_);
if v___x_416_ == 0 {
v_x_403_ = v_n_410_;
v_x_404_ = v_m_414_;
state = 0; continue;
} else {
let mut v___x_418_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_m_414_);
v___x_418_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_418_, 0, v_m_414_);
lean_ctor_set(v___x_418_, 1, v_x_405_);
v_x_403_ = v_n_410_;
v_x_404_ = v_m_414_;
v_x_405_ = v___x_418_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mkMapAux___boxed(mut v_freq_420_: *mut lean_object, mut v_x_421_: *mut lean_object, mut v_x_422_: *mut lean_object, mut v_x_423_: *mut lean_object) -> *mut lean_object{
let mut v_res_424_: *mut lean_object = core::ptr::null_mut(); 
v_res_424_ = l_mkMapAux(v_freq_420_, v_x_421_, v_x_422_, v_x_423_);
lean_dec(v_freq_420_);
return v_res_424_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkMap(mut v_n_425_: *mut lean_object, mut v_freq_426_: *mut lean_object) -> *mut lean_object{
let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); 
v___x_427_ = lean_box(0);
v___x_428_ = lean_box(0);
v___x_429_ = l_mkMapAux(v_freq_426_, v_n_425_, v___x_427_, v___x_428_);
return v___x_429_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkMap___boxed(mut v_n_430_: *mut lean_object, mut v_freq_431_: *mut lean_object) -> *mut lean_object{
let mut v_res_432_: *mut lean_object = core::ptr::null_mut(); 
v_res_432_ = l_mkMap(v_n_430_, v_freq_431_);
lean_dec(v_freq_431_);
return v_res_432_;
}
#[no_mangle] pub unsafe extern "C" fn l_myLen(mut v_x_433_: *mut lean_object, mut v_x_434_: *mut lean_object) -> *mut lean_object{
let mut v_head_435_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_436_: *mut lean_object = core::ptr::null_mut(); let mut v___x_437_: *mut lean_object = core::ptr::null_mut(); let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_440_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_433_) == 0 {
return v_x_434_;
} else {
let mut v_head_435_: *mut lean_object = core::ptr::null_mut(); 
v_head_435_ = lean_ctor_get(v_x_433_, 0);
if lean_obj_tag(v_head_435_) == 1 {
let mut v_tail_436_: *mut lean_object = core::ptr::null_mut(); let mut v___x_437_: *mut lean_object = core::ptr::null_mut(); let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); 
v_tail_436_ = lean_ctor_get(v_x_433_, 1);
v___x_437_ = lean_unsigned_to_nat(1);
v___x_438_ = lean_nat_add(v_x_434_, v___x_437_);
lean_dec(v_x_434_);
v_x_433_ = v_tail_436_;
v_x_434_ = v___x_438_;
state = 0; continue;
} else {
let mut v_tail_440_: *mut lean_object = core::ptr::null_mut(); 
v_tail_440_ = lean_ctor_get(v_x_433_, 1);
v_x_433_ = v_tail_440_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_myLen___boxed(mut v_x_442_: *mut lean_object, mut v_x_443_: *mut lean_object) -> *mut lean_object{
let mut v_res_444_: *mut lean_object = core::ptr::null_mut(); 
v_res_444_ = l_myLen(v_x_442_, v_x_443_);
lean_dec(v_x_442_);
return v_res_444_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v_x_445_: *mut lean_object, mut v_v_446_: u8, mut v_r_447_: *mut lean_object) -> *mut lean_object{
if v_v_446_ == 0 {
lean_inc(v_r_447_);
return v_r_447_;
} else {
let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); 
v___x_448_ = lean_unsigned_to_nat(1);
v___x_449_ = lean_nat_add(v_r_447_, v___x_448_);
return v___x_449_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0___boxed(mut v_x_450_: *mut lean_object, mut v_v_451_: *mut lean_object, mut v_r_452_: *mut lean_object) -> *mut lean_object{
let mut v_v_boxed_453_: u8 = 0; let mut v_res_454_: *mut lean_object = core::ptr::null_mut(); 
v_v_boxed_453_ = (lean_unbox(v_v_451_) as u8);
v_res_454_ = l_main___lam__0(v_x_450_, v_v_boxed_453_, v_r_452_);
lean_dec(v_r_452_);
lean_dec(v_x_450_);
return v_res_454_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_455_: *mut lean_object) -> *mut lean_object{
let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_458_: *mut lean_object = core::ptr::null_mut(); let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); 
v___x_457_ = lean_get_stdout();
v_putStr_458_ = lean_ctor_get(v___x_457_, 4);
lean_inc_ref(v_putStr_458_);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_apply_2(v_putStr_458_, v_s_455_, lean_box(0));
return v___x_459_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_460_: *mut lean_object, mut v_a_461_: *mut lean_object) -> *mut lean_object{
let mut v_res_462_: *mut lean_object = core::ptr::null_mut(); 
v_res_462_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_460_);
return v_res_462_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_463_: *mut lean_object) -> *mut lean_object{
let mut v___x_465_: u32 = 0; let mut v___x_466_: *mut lean_object = core::ptr::null_mut(); let mut v___x_467_: *mut lean_object = core::ptr::null_mut(); 
v___x_465_ = 10;
v___x_466_ = lean_string_push(v_s_463_, v___x_465_);
v___x_467_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_466_);
return v___x_467_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_468_: *mut lean_object, mut v_a_469_: *mut lean_object) -> *mut lean_object{
let mut v_res_470_: *mut lean_object = core::ptr::null_mut(); 
v_res_470_ = l_IO_println___at___00main_spec__0(v_s_468_);
return v_res_470_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_476_: *mut lean_object) -> *mut lean_object{
let mut v___x_479_: *mut lean_object = core::ptr::null_mut(); let mut v___x_480_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_481_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_482_: *mut lean_object = core::ptr::null_mut(); let mut v_head_483_: *mut lean_object = core::ptr::null_mut(); let mut v_head_484_: *mut lean_object = core::ptr::null_mut(); let mut v___f_485_: *mut lean_object = core::ptr::null_mut(); let mut v___x_486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: *mut lean_object = core::ptr::null_mut(); let mut v___x_489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v___y_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); let mut v___x_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); let mut v___x_499_: *mut lean_object = core::ptr::null_mut(); let mut v___x_500_: *mut lean_object = core::ptr::null_mut(); let mut v___x_501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: u8 = 0; let mut v___x_507_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_xs_476_) == 1 {
let mut v_tail_481_: *mut lean_object = core::ptr::null_mut(); 
v_tail_481_ = lean_ctor_get(v_xs_476_, 1);
lean_inc(v_tail_481_);
if lean_obj_tag(v_tail_481_) == 1 {
let mut v_tail_482_: *mut lean_object = core::ptr::null_mut(); 
v_tail_482_ = lean_ctor_get(v_tail_481_, 1);
if lean_obj_tag(v_tail_482_) == 0 {
let mut v_head_483_: *mut lean_object = core::ptr::null_mut(); let mut v_head_484_: *mut lean_object = core::ptr::null_mut(); let mut v___f_485_: *mut lean_object = core::ptr::null_mut(); let mut v___x_486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: *mut lean_object = core::ptr::null_mut(); let mut v___x_489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v___y_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: u8 = 0; 
v_head_483_ = lean_ctor_get(v_xs_476_, 0);
lean_inc(v_head_483_);
lean_dec_ref_known(v_xs_476_, 2);
v_head_484_ = lean_ctor_get(v_tail_481_, 0);
lean_inc(v_head_484_);
lean_dec_ref_known(v_tail_481_, 2);
v___f_485_ = l_main___closed__2;
v___x_486_ = lean_box(0);
v___x_487_ = lean_unsigned_to_nat(0);
v___x_488_ = lean_string_utf8_byte_size(v_head_483_);
v___x_489_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_489_, 0, v_head_483_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
lean_ctor_set(v___x_489_, 2, v___x_488_);
v___x_490_ = l_String_Slice_toNat_x21(v___x_489_);
lean_dec_ref_known(v___x_489_, 3);
v___x_503_ = lean_string_utf8_byte_size(v_head_484_);
v___x_504_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_504_, 0, v_head_484_);
lean_ctor_set(v___x_504_, 1, v___x_487_);
lean_ctor_set(v___x_504_, 2, v___x_503_);
v___x_505_ = l_String_Slice_toNat_x21(v___x_504_);
lean_dec_ref_known(v___x_504_, 3);
v___x_506_ = lean_nat_dec_eq(v___x_505_, v___x_487_);
if v___x_506_ == 0 {
v___y_492_ = v___x_505_;
state = 2; continue;
} else {
let mut v___x_507_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_505_);
v___x_507_ = lean_unsigned_to_nat(1);
v___y_492_ = v___x_507_;
state = 2; continue;
}
} else {
lean_dec_ref_known(v_tail_481_, 2);
lean_dec_ref_known(v_xs_476_, 2);
state = 1; continue;
}
} else {
lean_dec_ref_known(v_xs_476_, 2);
lean_dec(v_tail_481_);
state = 1; continue;
}
} else {
lean_dec(v_xs_476_);
state = 1; continue;
}
}
1 => {
v___x_479_ = l_main___closed__1;
v___x_480_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
2 => {
v___x_493_ = l_mkMap(v___x_490_, v___y_492_);
lean_dec(v___y_492_);
v___x_494_ = l_List_head_x21___redArg(v___x_486_, v___x_493_);
v___x_495_ = l_fold___redArg(v___f_485_, v___x_494_, v___x_487_);
v___x_496_ = l_myLen(v___x_493_, v___x_487_);
lean_dec(v___x_493_);
v___x_497_ = l_Nat_reprFast(v___x_496_);
v___x_498_ = l_main___closed__3;
v___x_499_ = lean_string_append(v___x_497_, v___x_498_);
v___x_500_ = l_Nat_reprFast(v___x_495_);
v___x_501_ = lean_string_append(v___x_499_, v___x_500_);
lean_dec_ref(v___x_500_);
v___x_502_ = l_IO_println___at___00main_spec__0(v___x_501_);
return v___x_502_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_508_: *mut lean_object, mut v_a_509_: *mut lean_object) -> *mut lean_object{
let mut v_res_510_: *mut lean_object = core::ptr::null_mut(); 
v_res_510_ = _lean_main(v_xs_508_);
return v_res_510_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_rbmap__checkpoint(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_instInhabitedTree_default = _init_l_instInhabitedTree_default();
lean_mark_persistent(l_instInhabitedTree_default);
l_instInhabitedTree = _init_l_instInhabitedTree();
lean_mark_persistent(l_instInhabitedTree);
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
  let res = initialize_rbmap__checkpoint(1 /* builtin */);
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
