// Lean compiler output
// Module: rbmap
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
#[no_mangle] pub unsafe extern "C" fn l_balance1(mut v_x_112_: *mut lean_object, mut v_x_113_: u8, mut v_x_114_: *mut lean_object, mut v_x_115_: *mut lean_object) -> *mut lean_object{
let mut v_kv_117_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_118_: u8 = 0; let mut v_t_119_: *mut lean_object = core::ptr::null_mut(); let mut v_l_120_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_121_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_122_: u8 = 0; let mut v_r_u2081_123_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_124_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_125_: u8 = 0; let mut v_r_u2082_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: u8 = 0; let mut v___x_128_: u8 = 0; let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v_a_132_: *mut lean_object = core::ptr::null_mut(); let mut v_a_133_: *mut lean_object = core::ptr::null_mut(); let mut v_a_134_: u8 = 0; let mut v_a_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_138_: u8 = 0; let mut v_kv_140_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_141_: u8 = 0; let mut v_t_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: u8 = 0; let mut v___x_144_: u8 = 0; let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_148_: *mut lean_object = core::ptr::null_mut(); let mut v_a_149_: u8 = 0; let mut v_a_150_: *mut lean_object = core::ptr::null_mut(); let mut v_a_151_: *mut lean_object = core::ptr::null_mut(); let mut v_a_152_: u8 = 0; let mut v_a_153_: *mut lean_object = core::ptr::null_mut(); let mut v_a_154_: u8 = 0; let mut v_a_155_: *mut lean_object = core::ptr::null_mut(); let mut v_a_156_: *mut lean_object = core::ptr::null_mut(); let mut v_a_157_: u8 = 0; let mut v_a_158_: *mut lean_object = core::ptr::null_mut(); let mut v_a_159_: u8 = 0; let mut v_a_160_: *mut lean_object = core::ptr::null_mut(); let mut v_a_161_: *mut lean_object = core::ptr::null_mut(); let mut v_a_162_: u8 = 0; let mut v_a_163_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_164_: u8 = 0; let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_115_) == 1 {
let mut v_a_132_: *mut lean_object = core::ptr::null_mut(); let mut v_a_133_: *mut lean_object = core::ptr::null_mut(); let mut v_a_134_: u8 = 0; let mut v_a_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_138_: u8 = 0; let mut v_isSharedCheck_164_: u8 = 0; 
v_a_132_ = lean_ctor_get(v_x_115_, 0);
v_a_133_ = lean_ctor_get(v_x_115_, 1);
v_a_134_ = lean_ctor_get_uint8(v_x_115_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_135_ = lean_ctor_get(v_x_115_, 2);
v_isSharedCheck_164_ = (!lean_is_exclusive(v_x_115_)) as u8;
if v_isSharedCheck_164_ == 0 {
v___x_137_ = v_x_115_;
v_isShared_138_ = v_isSharedCheck_164_;
state = 2; continue;
} else {
lean_inc(v_a_135_);
lean_inc(v_a_133_);
lean_inc(v_a_132_);
lean_dec(v_x_115_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_164_;
state = 2; continue;
}
} else {
let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_115_);
lean_dec(v_x_114_);
lean_dec(v_x_112_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
}
1 => {
v___x_127_ = 0;
v___x_128_ = 1;
v___x_129_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_129_, 0, v_l_120_);
lean_ctor_set(v___x_129_, 1, v_kx_121_);
lean_ctor_set(v___x_129_, 2, v_r_u2081_123_);
lean_ctor_set_uint8(v___x_129_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_128_);
lean_ctor_set_uint8(v___x_129_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_122_);
v___x_130_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_130_, 0, v_r_u2082_126_);
lean_ctor_set(v___x_130_, 1, v_kv_117_);
lean_ctor_set(v___x_130_, 2, v_t_119_);
lean_ctor_set_uint8(v___x_130_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_128_);
lean_ctor_set_uint8(v___x_130_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vv_118_);
v___x_131_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v_ky_124_);
lean_ctor_set(v___x_131_, 2, v___x_130_);
lean_ctor_set_uint8(v___x_131_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_127_);
lean_ctor_set_uint8(v___x_131_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vy_125_);
return v___x_131_;
}
2 => {
if lean_obj_tag(v_a_132_) == 1 {
let mut v_a_149_: u8 = 0; 
v_a_149_ = lean_ctor_get_uint8(v_a_132_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_149_ == 0 {
let mut v_a_150_: *mut lean_object = core::ptr::null_mut(); let mut v_a_151_: *mut lean_object = core::ptr::null_mut(); let mut v_a_152_: u8 = 0; let mut v_a_153_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_137_);
v_a_150_ = lean_ctor_get(v_a_132_, 0);
lean_inc(v_a_150_);
v_a_151_ = lean_ctor_get(v_a_132_, 1);
lean_inc(v_a_151_);
v_a_152_ = lean_ctor_get_uint8(v_a_132_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_153_ = lean_ctor_get(v_a_132_, 2);
lean_inc(v_a_153_);
lean_dec_ref_known(v_a_132_, 3);
v_kv_117_ = v_x_112_;
v_vv_118_ = v_x_113_;
v_t_119_ = v_x_114_;
v_l_120_ = v_a_150_;
v_kx_121_ = v_a_151_;
v_vx_122_ = v_a_152_;
v_r_u2081_123_ = v_a_153_;
v_ky_124_ = v_a_133_;
v_vy_125_ = v_a_134_;
v_r_u2082_126_ = v_a_135_;
state = 1; continue;
} else {
if lean_obj_tag(v_a_135_) == 1 {
let mut v_a_154_: u8 = 0; 
v_a_154_ = lean_ctor_get_uint8(v_a_135_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_154_ == 0 {
let mut v_a_155_: *mut lean_object = core::ptr::null_mut(); let mut v_a_156_: *mut lean_object = core::ptr::null_mut(); let mut v_a_157_: u8 = 0; let mut v_a_158_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_137_);
v_a_155_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_a_155_);
v_a_156_ = lean_ctor_get(v_a_135_, 1);
lean_inc(v_a_156_);
v_a_157_ = lean_ctor_get_uint8(v_a_135_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_158_ = lean_ctor_get(v_a_135_, 2);
lean_inc(v_a_158_);
lean_dec_ref_known(v_a_135_, 3);
v_kv_117_ = v_x_112_;
v_vv_118_ = v_x_113_;
v_t_119_ = v_x_114_;
v_l_120_ = v_a_132_;
v_kx_121_ = v_a_133_;
v_vx_122_ = v_a_134_;
v_r_u2081_123_ = v_a_155_;
v_ky_124_ = v_a_156_;
v_vy_125_ = v_a_157_;
v_r_u2082_126_ = v_a_158_;
state = 1; continue;
} else {
v_kv_140_ = v_x_112_;
v_vv_141_ = v_x_113_;
v_t_142_ = v_x_114_;
state = 3; continue;
}
} else {
v_kv_140_ = v_x_112_;
v_vv_141_ = v_x_113_;
v_t_142_ = v_x_114_;
state = 3; continue;
}
}
} else {
if lean_obj_tag(v_a_135_) == 1 {
let mut v_a_159_: u8 = 0; 
v_a_159_ = lean_ctor_get_uint8(v_a_135_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_159_ == 0 {
let mut v_a_160_: *mut lean_object = core::ptr::null_mut(); let mut v_a_161_: *mut lean_object = core::ptr::null_mut(); let mut v_a_162_: u8 = 0; let mut v_a_163_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_137_);
v_a_160_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_a_160_);
v_a_161_ = lean_ctor_get(v_a_135_, 1);
lean_inc(v_a_161_);
v_a_162_ = lean_ctor_get_uint8(v_a_135_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_163_ = lean_ctor_get(v_a_135_, 2);
lean_inc(v_a_163_);
lean_dec_ref_known(v_a_135_, 3);
v_kv_117_ = v_x_112_;
v_vv_118_ = v_x_113_;
v_t_119_ = v_x_114_;
v_l_120_ = v_a_132_;
v_kx_121_ = v_a_133_;
v_vx_122_ = v_a_134_;
v_r_u2081_123_ = v_a_160_;
v_ky_124_ = v_a_161_;
v_vy_125_ = v_a_162_;
v_r_u2082_126_ = v_a_163_;
state = 1; continue;
} else {
v_kv_140_ = v_x_112_;
v_vv_141_ = v_x_113_;
v_t_142_ = v_x_114_;
state = 3; continue;
}
} else {
v_kv_140_ = v_x_112_;
v_vv_141_ = v_x_113_;
v_t_142_ = v_x_114_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_balance1___boxed(mut v_x_166_: *mut lean_object, mut v_x_167_: *mut lean_object, mut v_x_168_: *mut lean_object, mut v_x_169_: *mut lean_object) -> *mut lean_object{
let mut v_x_136__boxed_170_: u8 = 0; let mut v_res_171_: *mut lean_object = core::ptr::null_mut(); 
v_x_136__boxed_170_ = (lean_unbox(v_x_167_) as u8);
v_res_171_ = l_balance1(v_x_166_, v_x_136__boxed_170_, v_x_168_, v_x_169_);
return v_res_171_;
}
#[no_mangle] pub unsafe extern "C" fn l_balance2(mut v_x_172_: *mut lean_object, mut v_x_173_: *mut lean_object, mut v_x_174_: u8, mut v_x_175_: *mut lean_object) -> *mut lean_object{
let mut v_t_177_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_178_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_179_: u8 = 0; let mut v_l_180_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_u2081_181_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_u2081_182_: u8 = 0; let mut v_r_u2081_183_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_184_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_185_: u8 = 0; let mut v_r_u2082_186_: *mut lean_object = core::ptr::null_mut(); let mut v___x_187_: u8 = 0; let mut v___x_188_: u8 = 0; let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v_a_192_: *mut lean_object = core::ptr::null_mut(); let mut v_a_193_: *mut lean_object = core::ptr::null_mut(); let mut v_a_194_: u8 = 0; let mut v_a_195_: *mut lean_object = core::ptr::null_mut(); let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_198_: u8 = 0; let mut v_t_200_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_201_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_202_: u8 = 0; let mut v___x_203_: u8 = 0; let mut v___x_204_: u8 = 0; let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); let mut v___x_207_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_208_: *mut lean_object = core::ptr::null_mut(); let mut v_a_209_: u8 = 0; let mut v_a_210_: *mut lean_object = core::ptr::null_mut(); let mut v_a_211_: *mut lean_object = core::ptr::null_mut(); let mut v_a_212_: u8 = 0; let mut v_a_213_: *mut lean_object = core::ptr::null_mut(); let mut v_a_214_: u8 = 0; let mut v_a_215_: *mut lean_object = core::ptr::null_mut(); let mut v_a_216_: *mut lean_object = core::ptr::null_mut(); let mut v_a_217_: u8 = 0; let mut v_a_218_: *mut lean_object = core::ptr::null_mut(); let mut v_a_219_: u8 = 0; let mut v_a_220_: *mut lean_object = core::ptr::null_mut(); let mut v_a_221_: *mut lean_object = core::ptr::null_mut(); let mut v_a_222_: u8 = 0; let mut v_a_223_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_224_: u8 = 0; let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_175_) == 1 {
let mut v_a_192_: *mut lean_object = core::ptr::null_mut(); let mut v_a_193_: *mut lean_object = core::ptr::null_mut(); let mut v_a_194_: u8 = 0; let mut v_a_195_: *mut lean_object = core::ptr::null_mut(); let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_198_: u8 = 0; let mut v_isSharedCheck_224_: u8 = 0; 
v_a_192_ = lean_ctor_get(v_x_175_, 0);
v_a_193_ = lean_ctor_get(v_x_175_, 1);
v_a_194_ = lean_ctor_get_uint8(v_x_175_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_195_ = lean_ctor_get(v_x_175_, 2);
v_isSharedCheck_224_ = (!lean_is_exclusive(v_x_175_)) as u8;
if v_isSharedCheck_224_ == 0 {
v___x_197_ = v_x_175_;
v_isShared_198_ = v_isSharedCheck_224_;
state = 2; continue;
} else {
lean_inc(v_a_195_);
lean_inc(v_a_193_);
lean_inc(v_a_192_);
lean_dec(v_x_175_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_224_;
state = 2; continue;
}
} else {
let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_175_);
lean_dec(v_x_173_);
lean_dec(v_x_172_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
}
1 => {
v___x_187_ = 0;
v___x_188_ = 1;
v___x_189_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_189_, 0, v_t_177_);
lean_ctor_set(v___x_189_, 1, v_kv_178_);
lean_ctor_set(v___x_189_, 2, v_l_180_);
lean_ctor_set_uint8(v___x_189_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_188_);
lean_ctor_set_uint8(v___x_189_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vv_179_);
v___x_190_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_190_, 0, v_r_u2081_183_);
lean_ctor_set(v___x_190_, 1, v_ky_184_);
lean_ctor_set(v___x_190_, 2, v_r_u2082_186_);
lean_ctor_set_uint8(v___x_190_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_188_);
lean_ctor_set_uint8(v___x_190_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vy_185_);
v___x_191_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v_kx_u2081_181_);
lean_ctor_set(v___x_191_, 2, v___x_190_);
lean_ctor_set_uint8(v___x_191_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_187_);
lean_ctor_set_uint8(v___x_191_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_u2081_182_);
return v___x_191_;
}
2 => {
if lean_obj_tag(v_a_192_) == 1 {
let mut v_a_209_: u8 = 0; 
v_a_209_ = lean_ctor_get_uint8(v_a_192_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_209_ == 0 {
let mut v_a_210_: *mut lean_object = core::ptr::null_mut(); let mut v_a_211_: *mut lean_object = core::ptr::null_mut(); let mut v_a_212_: u8 = 0; let mut v_a_213_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_197_);
v_a_210_ = lean_ctor_get(v_a_192_, 0);
lean_inc(v_a_210_);
v_a_211_ = lean_ctor_get(v_a_192_, 1);
lean_inc(v_a_211_);
v_a_212_ = lean_ctor_get_uint8(v_a_192_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_213_ = lean_ctor_get(v_a_192_, 2);
lean_inc(v_a_213_);
lean_dec_ref_known(v_a_192_, 3);
v_t_177_ = v_x_172_;
v_kv_178_ = v_x_173_;
v_vv_179_ = v_x_174_;
v_l_180_ = v_a_210_;
v_kx_u2081_181_ = v_a_211_;
v_vx_u2081_182_ = v_a_212_;
v_r_u2081_183_ = v_a_213_;
v_ky_184_ = v_a_193_;
v_vy_185_ = v_a_194_;
v_r_u2082_186_ = v_a_195_;
state = 1; continue;
} else {
if lean_obj_tag(v_a_195_) == 1 {
let mut v_a_214_: u8 = 0; 
v_a_214_ = lean_ctor_get_uint8(v_a_195_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_214_ == 0 {
let mut v_a_215_: *mut lean_object = core::ptr::null_mut(); let mut v_a_216_: *mut lean_object = core::ptr::null_mut(); let mut v_a_217_: u8 = 0; let mut v_a_218_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_197_);
v_a_215_ = lean_ctor_get(v_a_195_, 0);
lean_inc(v_a_215_);
v_a_216_ = lean_ctor_get(v_a_195_, 1);
lean_inc(v_a_216_);
v_a_217_ = lean_ctor_get_uint8(v_a_195_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_218_ = lean_ctor_get(v_a_195_, 2);
lean_inc(v_a_218_);
lean_dec_ref_known(v_a_195_, 3);
v_t_177_ = v_x_172_;
v_kv_178_ = v_x_173_;
v_vv_179_ = v_x_174_;
v_l_180_ = v_a_192_;
v_kx_u2081_181_ = v_a_193_;
v_vx_u2081_182_ = v_a_194_;
v_r_u2081_183_ = v_a_215_;
v_ky_184_ = v_a_216_;
v_vy_185_ = v_a_217_;
v_r_u2082_186_ = v_a_218_;
state = 1; continue;
} else {
v_t_200_ = v_x_172_;
v_kv_201_ = v_x_173_;
v_vv_202_ = v_x_174_;
state = 3; continue;
}
} else {
v_t_200_ = v_x_172_;
v_kv_201_ = v_x_173_;
v_vv_202_ = v_x_174_;
state = 3; continue;
}
}
} else {
if lean_obj_tag(v_a_195_) == 1 {
let mut v_a_219_: u8 = 0; 
v_a_219_ = lean_ctor_get_uint8(v_a_195_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_219_ == 0 {
let mut v_a_220_: *mut lean_object = core::ptr::null_mut(); let mut v_a_221_: *mut lean_object = core::ptr::null_mut(); let mut v_a_222_: u8 = 0; let mut v_a_223_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_197_);
v_a_220_ = lean_ctor_get(v_a_195_, 0);
lean_inc(v_a_220_);
v_a_221_ = lean_ctor_get(v_a_195_, 1);
lean_inc(v_a_221_);
v_a_222_ = lean_ctor_get_uint8(v_a_195_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_223_ = lean_ctor_get(v_a_195_, 2);
lean_inc(v_a_223_);
lean_dec_ref_known(v_a_195_, 3);
v_t_177_ = v_x_172_;
v_kv_178_ = v_x_173_;
v_vv_179_ = v_x_174_;
v_l_180_ = v_a_192_;
v_kx_u2081_181_ = v_a_193_;
v_vx_u2081_182_ = v_a_194_;
v_r_u2081_183_ = v_a_220_;
v_ky_184_ = v_a_221_;
v_vy_185_ = v_a_222_;
v_r_u2082_186_ = v_a_223_;
state = 1; continue;
} else {
v_t_200_ = v_x_172_;
v_kv_201_ = v_x_173_;
v_vv_202_ = v_x_174_;
state = 3; continue;
}
} else {
v_t_200_ = v_x_172_;
v_kv_201_ = v_x_173_;
v_vv_202_ = v_x_174_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_balance2___boxed(mut v_x_226_: *mut lean_object, mut v_x_227_: *mut lean_object, mut v_x_228_: *mut lean_object, mut v_x_229_: *mut lean_object) -> *mut lean_object{
let mut v_x_137__boxed_230_: u8 = 0; let mut v_res_231_: *mut lean_object = core::ptr::null_mut(); 
v_x_137__boxed_230_ = (lean_unbox(v_x_228_) as u8);
v_res_231_ = l_balance2(v_x_226_, v_x_227_, v_x_137__boxed_230_, v_x_229_);
return v_res_231_;
}
#[no_mangle] pub unsafe extern "C" fn l_isRed(mut v_x_232_: *mut lean_object) -> u8{
if lean_obj_tag(v_x_232_) == 1 {
let mut v_a_233_: u8 = 0; 
v_a_233_ = lean_ctor_get_uint8(v_x_232_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
if v_a_233_ == 0 {
let mut v___x_234_: u8 = 0; 
v___x_234_ = 1;
return v___x_234_;
} else {
let mut v___x_235_: u8 = 0; 
v___x_235_ = 0;
return v___x_235_;
}
} else {
let mut v___x_236_: u8 = 0; 
v___x_236_ = 0;
return v___x_236_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_isRed___boxed(mut v_x_237_: *mut lean_object) -> *mut lean_object{
let mut v_res_238_: u8 = 0; let mut v_r_239_: *mut lean_object = core::ptr::null_mut(); 
v_res_238_ = l_isRed(v_x_237_);
lean_dec(v_x_237_);
v_r_239_ = lean_box((v_res_238_) as usize);
return v_r_239_;
}
#[no_mangle] pub unsafe extern "C" fn l_ins(mut v_kx_240_: *mut lean_object, mut v_vx_241_: u8, mut v_x_242_: *mut lean_object) -> *mut lean_object{
let mut v___x_243_: u8 = 0; let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); let mut v_a_245_: u8 = 0; let mut v_a_246_: *mut lean_object = core::ptr::null_mut(); let mut v_a_247_: *mut lean_object = core::ptr::null_mut(); let mut v_a_248_: u8 = 0; let mut v_a_249_: *mut lean_object = core::ptr::null_mut(); let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_252_: u8 = 0; let mut v_t_254_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_255_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_256_: u8 = 0; let mut v_l_257_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_u2081_258_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_u2081_259_: u8 = 0; let mut v_r_u2081_260_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_261_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_262_: u8 = 0; let mut v_r_u2082_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: u8 = 0; let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_269_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_271_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_272_: u8 = 0; let mut v_t_273_: *mut lean_object = core::ptr::null_mut(); let mut v_l_274_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_275_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_276_: u8 = 0; let mut v_r_u2081_277_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_278_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_279_: u8 = 0; let mut v_r_u2082_280_: *mut lean_object = core::ptr::null_mut(); let mut v___x_281_: u8 = 0; let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); let mut v___x_283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_285_: u8 = 0; let mut v___x_286_: u8 = 0; let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: u8 = 0; let mut v___x_293_: u8 = 0; let mut v___x_294_: u8 = 0; let mut v___x_295_: *mut lean_object = core::ptr::null_mut(); let mut v___x_296_: *mut lean_object = core::ptr::null_mut(); let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v_a_298_: *mut lean_object = core::ptr::null_mut(); let mut v_a_299_: *mut lean_object = core::ptr::null_mut(); let mut v_a_300_: u8 = 0; let mut v_a_301_: *mut lean_object = core::ptr::null_mut(); let mut v___x_303_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_304_: u8 = 0; let mut v_t_306_: *mut lean_object = core::ptr::null_mut(); let mut v_kv_307_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_308_: u8 = 0; let mut v___x_309_: u8 = 0; let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_312_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_313_: *mut lean_object = core::ptr::null_mut(); let mut v_a_314_: u8 = 0; let mut v_a_315_: *mut lean_object = core::ptr::null_mut(); let mut v_a_316_: *mut lean_object = core::ptr::null_mut(); let mut v_a_317_: u8 = 0; let mut v_a_318_: *mut lean_object = core::ptr::null_mut(); let mut v_a_319_: u8 = 0; let mut v_a_320_: *mut lean_object = core::ptr::null_mut(); let mut v_a_321_: *mut lean_object = core::ptr::null_mut(); let mut v_a_322_: u8 = 0; let mut v_a_323_: *mut lean_object = core::ptr::null_mut(); let mut v_a_324_: u8 = 0; let mut v_a_325_: *mut lean_object = core::ptr::null_mut(); let mut v_a_326_: *mut lean_object = core::ptr::null_mut(); let mut v_a_327_: u8 = 0; let mut v_a_328_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_329_: u8 = 0; let mut v___x_330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_332_: u8 = 0; let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); let mut v_a_336_: *mut lean_object = core::ptr::null_mut(); let mut v_a_337_: *mut lean_object = core::ptr::null_mut(); let mut v_a_338_: u8 = 0; let mut v_a_339_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_342_: u8 = 0; let mut v_kv_344_: *mut lean_object = core::ptr::null_mut(); let mut v_vv_345_: u8 = 0; let mut v_t_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_347_: u8 = 0; let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_351_: *mut lean_object = core::ptr::null_mut(); let mut v_a_352_: u8 = 0; let mut v_a_353_: *mut lean_object = core::ptr::null_mut(); let mut v_a_354_: *mut lean_object = core::ptr::null_mut(); let mut v_a_355_: u8 = 0; let mut v_a_356_: *mut lean_object = core::ptr::null_mut(); let mut v_a_357_: u8 = 0; let mut v_a_358_: *mut lean_object = core::ptr::null_mut(); let mut v_a_359_: *mut lean_object = core::ptr::null_mut(); let mut v_a_360_: u8 = 0; let mut v_a_361_: *mut lean_object = core::ptr::null_mut(); let mut v_a_362_: u8 = 0; let mut v_a_363_: *mut lean_object = core::ptr::null_mut(); let mut v_a_364_: *mut lean_object = core::ptr::null_mut(); let mut v_a_365_: u8 = 0; let mut v_a_366_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_367_: u8 = 0; let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_369_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_242_) == 0 {
let mut v___x_243_: u8 = 0; let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); 
v___x_243_ = 0;
v___x_244_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_244_, 0, v_x_242_);
lean_ctor_set(v___x_244_, 1, v_kx_240_);
lean_ctor_set(v___x_244_, 2, v_x_242_);
lean_ctor_set_uint8(v___x_244_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v___x_243_);
lean_ctor_set_uint8(v___x_244_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_241_);
return v___x_244_;
} else {
let mut v_a_245_: u8 = 0; let mut v_a_246_: *mut lean_object = core::ptr::null_mut(); let mut v_a_247_: *mut lean_object = core::ptr::null_mut(); let mut v_a_248_: u8 = 0; let mut v_a_249_: *mut lean_object = core::ptr::null_mut(); let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_252_: u8 = 0; let mut v_isSharedCheck_369_: u8 = 0; 
v_a_245_ = lean_ctor_get_uint8(v_x_242_, (core::mem::size_of::<*mut lean_object>()*3) as u32);
v_a_246_ = lean_ctor_get(v_x_242_, 0);
v_a_247_ = lean_ctor_get(v_x_242_, 1);
v_a_248_ = lean_ctor_get_uint8(v_x_242_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_249_ = lean_ctor_get(v_x_242_, 2);
v_isSharedCheck_369_ = (!lean_is_exclusive(v_x_242_)) as u8;
if v_isSharedCheck_369_ == 0 {
v___x_251_ = v_x_242_;
v_isShared_252_ = v_isSharedCheck_369_;
state = 1; continue;
} else {
lean_inc(v_a_249_);
lean_inc(v_a_247_);
lean_inc(v_a_246_);
lean_dec(v_x_242_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_369_;
state = 1; continue;
}
}
}
1 => {
if v_a_245_ == 0 {
let mut v___x_285_: u8 = 0; 
lean_del_object(v___x_251_);
v___x_285_ = lean_nat_dec_lt(v_kx_240_, v_a_247_);
if v___x_285_ == 0 {
let mut v___x_286_: u8 = 0; 
v___x_286_ = lean_nat_dec_eq(v_kx_240_, v_a_247_);
if v___x_286_ == 0 {
let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); 
v___x_287_ = l_ins(v_kx_240_, v_vx_241_, v_a_249_);
v___x_288_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_288_, 0, v_a_246_);
lean_ctor_set(v___x_288_, 1, v_a_247_);
lean_ctor_set(v___x_288_, 2, v___x_287_);
lean_ctor_set_uint8(v___x_288_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_245_);
lean_ctor_set_uint8(v___x_288_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_248_);
return v___x_288_;
} else {
let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_247_);
v___x_289_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_289_, 0, v_a_246_);
lean_ctor_set(v___x_289_, 1, v_kx_240_);
lean_ctor_set(v___x_289_, 2, v_a_249_);
lean_ctor_set_uint8(v___x_289_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_245_);
lean_ctor_set_uint8(v___x_289_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_241_);
return v___x_289_;
}
} else {
let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); 
v___x_290_ = l_ins(v_kx_240_, v_vx_241_, v_a_246_);
v___x_291_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_a_247_);
lean_ctor_set(v___x_291_, 2, v_a_249_);
lean_ctor_set_uint8(v___x_291_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_245_);
lean_ctor_set_uint8(v___x_291_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_248_);
return v___x_291_;
}
} else {
let mut v___x_292_: u8 = 0; 
v___x_292_ = lean_nat_dec_lt(v_kx_240_, v_a_247_);
if v___x_292_ == 0 {
let mut v___x_293_: u8 = 0; 
v___x_293_ = lean_nat_dec_eq(v_kx_240_, v_a_247_);
if v___x_293_ == 0 {
let mut v___x_294_: u8 = 0; 
v___x_294_ = l_isRed(v_a_249_);
if v___x_294_ == 0 {
let mut v___x_295_: *mut lean_object = core::ptr::null_mut(); let mut v___x_296_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_251_);
v___x_295_ = l_ins(v_kx_240_, v_vx_241_, v_a_249_);
v___x_296_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_296_, 0, v_a_246_);
lean_ctor_set(v___x_296_, 1, v_a_247_);
lean_ctor_set(v___x_296_, 2, v___x_295_);
lean_ctor_set_uint8(v___x_296_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_245_);
lean_ctor_set_uint8(v___x_296_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_248_);
return v___x_296_;
} else {
let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); 
v___x_297_ = l_ins(v_kx_240_, v_vx_241_, v_a_249_);
if lean_obj_tag(v___x_297_) == 1 {
let mut v_a_298_: *mut lean_object = core::ptr::null_mut(); let mut v_a_299_: *mut lean_object = core::ptr::null_mut(); let mut v_a_300_: u8 = 0; let mut v_a_301_: *mut lean_object = core::ptr::null_mut(); let mut v___x_303_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_304_: u8 = 0; let mut v_isSharedCheck_329_: u8 = 0; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_a_299_ = lean_ctor_get(v___x_297_, 1);
v_a_300_ = lean_ctor_get_uint8(v___x_297_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_301_ = lean_ctor_get(v___x_297_, 2);
v_isSharedCheck_329_ = (!lean_is_exclusive(v___x_297_)) as u8;
if v_isSharedCheck_329_ == 0 {
v___x_303_ = v___x_297_;
v_isShared_304_ = v_isSharedCheck_329_;
state = 5; continue;
} else {
lean_inc(v_a_301_);
lean_inc(v_a_299_);
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_329_;
state = 5; continue;
}
} else {
let mut v___x_330_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_297_);
lean_del_object(v___x_251_);
lean_dec(v_a_247_);
lean_dec(v_a_246_);
v___x_330_ = lean_box(0);
return v___x_330_;
}
}
} else {
let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_251_);
lean_dec(v_a_247_);
v___x_331_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_331_, 0, v_a_246_);
lean_ctor_set(v___x_331_, 1, v_kx_240_);
lean_ctor_set(v___x_331_, 2, v_a_249_);
lean_ctor_set_uint8(v___x_331_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_245_);
lean_ctor_set_uint8(v___x_331_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_vx_241_);
return v___x_331_;
}
} else {
let mut v___x_332_: u8 = 0; 
lean_del_object(v___x_251_);
v___x_332_ = l_isRed(v_a_246_);
if v___x_332_ == 0 {
let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: *mut lean_object = core::ptr::null_mut(); 
v___x_333_ = l_ins(v_kx_240_, v_vx_241_, v_a_246_);
v___x_334_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_a_247_);
lean_ctor_set(v___x_334_, 2, v_a_249_);
lean_ctor_set_uint8(v___x_334_, (core::mem::size_of::<*mut lean_object>()*3) as u32, v_a_245_);
lean_ctor_set_uint8(v___x_334_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_248_);
return v___x_334_;
} else {
let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); 
v___x_335_ = l_ins(v_kx_240_, v_vx_241_, v_a_246_);
if lean_obj_tag(v___x_335_) == 1 {
let mut v_a_336_: *mut lean_object = core::ptr::null_mut(); let mut v_a_337_: *mut lean_object = core::ptr::null_mut(); let mut v_a_338_: u8 = 0; let mut v_a_339_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_342_: u8 = 0; let mut v_isSharedCheck_367_: u8 = 0; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_a_337_ = lean_ctor_get(v___x_335_, 1);
v_a_338_ = lean_ctor_get_uint8(v___x_335_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_339_ = lean_ctor_get(v___x_335_, 2);
v_isSharedCheck_367_ = (!lean_is_exclusive(v___x_335_)) as u8;
if v_isSharedCheck_367_ == 0 {
v___x_341_ = v___x_335_;
v_isShared_342_ = v_isSharedCheck_367_;
state = 8; continue;
} else {
lean_inc(v_a_339_);
lean_inc(v_a_337_);
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_367_;
state = 8; continue;
}
} else {
let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_335_);
lean_dec(v_a_249_);
lean_dec(v_a_247_);
v___x_368_ = lean_box(0);
return v___x_368_;
}
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ins___boxed(mut v_kx_370_: *mut lean_object, mut v_vx_371_: *mut lean_object, mut v_x_372_: *mut lean_object) -> *mut lean_object{
let mut v_vx_boxed_373_: u8 = 0; let mut v_res_374_: *mut lean_object = core::ptr::null_mut(); 
v_vx_boxed_373_ = (lean_unbox(v_vx_371_) as u8);
v_res_374_ = l_ins(v_kx_370_, v_vx_boxed_373_, v_x_372_);
return v_res_374_;
}
#[no_mangle] pub unsafe extern "C" fn l_setBlack(mut v_x_375_: *mut lean_object) -> *mut lean_object{
let mut v_a_376_: *mut lean_object = core::ptr::null_mut(); let mut v_a_377_: *mut lean_object = core::ptr::null_mut(); let mut v_a_378_: u8 = 0; let mut v_a_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_382_: u8 = 0; let mut v___x_383_: u8 = 0; let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_386_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_387_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_375_) == 1 {
let mut v_a_376_: *mut lean_object = core::ptr::null_mut(); let mut v_a_377_: *mut lean_object = core::ptr::null_mut(); let mut v_a_378_: u8 = 0; let mut v_a_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_382_: u8 = 0; let mut v_isSharedCheck_387_: u8 = 0; 
v_a_376_ = lean_ctor_get(v_x_375_, 0);
v_a_377_ = lean_ctor_get(v_x_375_, 1);
v_a_378_ = lean_ctor_get_uint8(v_x_375_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32);
v_a_379_ = lean_ctor_get(v_x_375_, 2);
v_isSharedCheck_387_ = (!lean_is_exclusive(v_x_375_)) as u8;
if v_isSharedCheck_387_ == 0 {
v___x_381_ = v_x_375_;
v_isShared_382_ = v_isSharedCheck_387_;
state = 1; continue;
} else {
lean_inc(v_a_379_);
lean_inc(v_a_377_);
lean_inc(v_a_376_);
lean_dec(v_x_375_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_387_;
state = 1; continue;
}
} else {
return v_x_375_;
}
}
1 => {
v___x_383_ = 1;
if v_isShared_382_ == 0 {
v___x_385_ = v___x_381_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_386_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 3, (2) as u32);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_376_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_a_377_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_a_379_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, (core::mem::size_of::<*mut lean_object>()*3 + 1) as u32, v_a_378_);
v___x_385_ = v_reuseFailAlloc_386_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_insert(mut v_k_388_: *mut lean_object, mut v_v_389_: u8, mut v_t_390_: *mut lean_object) -> *mut lean_object{
let mut v___x_391_: u8 = 0; 
v___x_391_ = l_isRed(v_t_390_);
if v___x_391_ == 0 {
let mut v___x_392_: *mut lean_object = core::ptr::null_mut(); 
v___x_392_ = l_ins(v_k_388_, v_v_389_, v_t_390_);
return v___x_392_;
} else {
let mut v___x_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); 
v___x_393_ = l_ins(v_k_388_, v_v_389_, v_t_390_);
v___x_394_ = l_setBlack(v___x_393_);
return v___x_394_;
}
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
pub unsafe extern "C" fn initialize_rbmap(builtin: u8) -> *mut lean_object {
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
  let res = initialize_rbmap(1 /* builtin */);
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
