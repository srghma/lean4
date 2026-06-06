// Lean compiler output
// Module: rbmap_library
// Imports: public import Init public meta import Init public import Lean.Data.RBMap
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Lean_RBNode_isRed___redArg(_: *mut lean_object) -> u8;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Lean_RBNode_setBlack___redArg(_: *mut lean_object) -> *mut lean_object;
    fn l_List_head_x21___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg___lam__0(mut v_x_1_: *mut lean_object, mut v_y_2_: *mut lean_object) -> u8{
let mut v___x_3_: u8 = 0; 
v___x_3_ = lean_nat_dec_lt(v_x_1_, v_y_2_);
if v___x_3_ == 0 {
let mut v___x_4_: u8 = 0; 
v___x_4_ = lean_nat_dec_eq(v_x_1_, v_y_2_);
if v___x_4_ == 0 {
let mut v___x_5_: u8 = 0; 
v___x_5_ = 2;
return v___x_5_;
} else {
let mut v___x_6_: u8 = 0; 
v___x_6_ = 1;
return v___x_6_;
}
} else {
let mut v___x_7_: u8 = 0; 
v___x_7_ = 0;
return v___x_7_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg___lam__0___boxed(mut v_x_8_: *mut lean_object, mut v_y_9_: *mut lean_object) -> *mut lean_object{
let mut v_res_10_: u8 = 0; let mut v_r_11_: *mut lean_object = core::ptr::null_mut(); 
v_res_10_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg___lam__0(v_x_8_, v_y_9_);
lean_dec(v_y_9_);
lean_dec(v_x_8_);
v_r_11_ = lean_box((v_res_10_) as usize);
return v_r_11_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg(mut v_x_12_: *mut lean_object, mut v_x_13_: *mut lean_object, mut v_x_14_: *mut lean_object) -> *mut lean_object{
let mut v___x_15_: u8 = 0; let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v_color_17_: u8 = 0; let mut v_lchild_18_: *mut lean_object = core::ptr::null_mut(); let mut v_key_19_: *mut lean_object = core::ptr::null_mut(); let mut v_val_20_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_24_: u8 = 0; let mut v___x_25_: u8 = 0; let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_36_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_37_: u8 = 0; let mut v_lchild_38_: *mut lean_object = core::ptr::null_mut(); let mut v_key_39_: *mut lean_object = core::ptr::null_mut(); let mut v_val_40_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_44_: u8 = 0; let mut v___x_45_: u8 = 0; let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v_color_47_: u8 = 0; let mut v_lchild_48_: *mut lean_object = core::ptr::null_mut(); let mut v_key_49_: *mut lean_object = core::ptr::null_mut(); let mut v_val_50_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_51_: *mut lean_object = core::ptr::null_mut(); let mut v_a_53_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_54_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_55_: *mut lean_object = core::ptr::null_mut(); let mut v_b_56_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_57_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_58_: *mut lean_object = core::ptr::null_mut(); let mut v_c_59_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_60_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_61_: *mut lean_object = core::ptr::null_mut(); let mut v_d_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_67_: *mut lean_object = core::ptr::null_mut(); let mut v_color_68_: u8 = 0; let mut v_lchild_69_: *mut lean_object = core::ptr::null_mut(); let mut v_key_70_: *mut lean_object = core::ptr::null_mut(); let mut v_val_71_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_72_: *mut lean_object = core::ptr::null_mut(); let mut v_color_73_: u8 = 0; let mut v_lchild_74_: *mut lean_object = core::ptr::null_mut(); let mut v_key_75_: *mut lean_object = core::ptr::null_mut(); let mut v_val_76_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_80_: u8 = 0; let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_83_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_84_: u8 = 0; let mut v_unused_85_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_86_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_87_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_91_: u8 = 0; let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_94_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_95_: u8 = 0; let mut v_unused_96_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_97_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_98_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_99_: *mut lean_object = core::ptr::null_mut(); let mut v_color_100_: u8 = 0; let mut v_lchild_101_: *mut lean_object = core::ptr::null_mut(); let mut v_key_102_: *mut lean_object = core::ptr::null_mut(); let mut v_val_103_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_107_: u8 = 0; let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_110_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_111_: u8 = 0; let mut v_unused_112_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_113_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_114_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v_color_125_: u8 = 0; let mut v_lchild_126_: *mut lean_object = core::ptr::null_mut(); let mut v_key_127_: *mut lean_object = core::ptr::null_mut(); let mut v_val_128_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_129_: *mut lean_object = core::ptr::null_mut(); let mut v_a_131_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_132_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_133_: *mut lean_object = core::ptr::null_mut(); let mut v_b_134_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_135_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_136_: *mut lean_object = core::ptr::null_mut(); let mut v_c_137_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_138_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_139_: *mut lean_object = core::ptr::null_mut(); let mut v_d_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_145_: *mut lean_object = core::ptr::null_mut(); let mut v_color_146_: u8 = 0; let mut v_lchild_147_: *mut lean_object = core::ptr::null_mut(); let mut v_key_148_: *mut lean_object = core::ptr::null_mut(); let mut v_val_149_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_150_: *mut lean_object = core::ptr::null_mut(); let mut v_color_151_: u8 = 0; let mut v_lchild_152_: *mut lean_object = core::ptr::null_mut(); let mut v_key_153_: *mut lean_object = core::ptr::null_mut(); let mut v_val_154_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_158_: u8 = 0; let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_161_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_162_: u8 = 0; let mut v_unused_163_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_164_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_165_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_169_: u8 = 0; let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_172_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_173_: u8 = 0; let mut v_unused_174_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_175_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_176_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_177_: *mut lean_object = core::ptr::null_mut(); let mut v_color_178_: u8 = 0; let mut v_lchild_179_: *mut lean_object = core::ptr::null_mut(); let mut v_key_180_: *mut lean_object = core::ptr::null_mut(); let mut v_val_181_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_185_: u8 = 0; let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_188_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_189_: u8 = 0; let mut v_unused_190_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_191_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_192_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_193_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); let mut v___x_195_: *mut lean_object = core::ptr::null_mut(); let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_198_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_199_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_12_) == 0 {
let mut v___x_15_: u8 = 0; let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); 
v___x_15_ = 0;
v___x_16_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_16_, 0, v_x_12_);
lean_ctor_set(v___x_16_, 1, v_x_13_);
lean_ctor_set(v___x_16_, 2, v_x_14_);
lean_ctor_set(v___x_16_, 3, v_x_12_);
lean_ctor_set_uint8(v___x_16_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v___x_15_);
return v___x_16_;
} else {
let mut v_color_17_: u8 = 0; 
v_color_17_ = lean_ctor_get_uint8(v_x_12_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_17_ == 0 {
let mut v_lchild_18_: *mut lean_object = core::ptr::null_mut(); let mut v_key_19_: *mut lean_object = core::ptr::null_mut(); let mut v_val_20_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_24_: u8 = 0; let mut v_isSharedCheck_37_: u8 = 0; 
v_lchild_18_ = lean_ctor_get(v_x_12_, 0);
v_key_19_ = lean_ctor_get(v_x_12_, 1);
v_val_20_ = lean_ctor_get(v_x_12_, 2);
v_rchild_21_ = lean_ctor_get(v_x_12_, 3);
v_isSharedCheck_37_ = (!lean_is_exclusive(v_x_12_)) as u8;
if v_isSharedCheck_37_ == 0 {
v___x_23_ = v_x_12_;
v_isShared_24_ = v_isSharedCheck_37_;
state = 1; continue;
} else {
lean_inc(v_rchild_21_);
lean_inc(v_val_20_);
lean_inc(v_key_19_);
lean_inc(v_lchild_18_);
lean_dec(v_x_12_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_37_;
state = 1; continue;
}
} else {
let mut v_lchild_38_: *mut lean_object = core::ptr::null_mut(); let mut v_key_39_: *mut lean_object = core::ptr::null_mut(); let mut v_val_40_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_44_: u8 = 0; let mut v_isSharedCheck_199_: u8 = 0; 
v_lchild_38_ = lean_ctor_get(v_x_12_, 0);
v_key_39_ = lean_ctor_get(v_x_12_, 1);
v_val_40_ = lean_ctor_get(v_x_12_, 2);
v_rchild_41_ = lean_ctor_get(v_x_12_, 3);
v_isSharedCheck_199_ = (!lean_is_exclusive(v_x_12_)) as u8;
if v_isSharedCheck_199_ == 0 {
v___x_43_ = v_x_12_;
v_isShared_44_ = v_isSharedCheck_199_;
state = 5; continue;
} else {
lean_inc(v_rchild_41_);
lean_inc(v_val_40_);
lean_inc(v_key_39_);
lean_inc(v_lchild_38_);
lean_dec(v_x_12_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_199_;
state = 5; continue;
}
}
}
}
1 => {
v___x_25_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg___lam__0(v_x_13_, v_key_19_);
match v___x_25_
{
0 => {
let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
v___x_26_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg(v_lchild_18_, v_x_13_, v_x_14_);
if v_isShared_24_ == 0 {
lean_ctor_set(v___x_23_, 0, v___x_26_);
v___x_28_ = v___x_23_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_29_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_key_19_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v_val_20_);
lean_ctor_set(v_reuseFailAlloc_29_, 3, v_rchild_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_29_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
v___x_28_ = v_reuseFailAlloc_29_;
state = 2; continue;
}
}
1 => {
let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_val_20_);
lean_dec(v_key_19_);
if v_isShared_24_ == 0 {
lean_ctor_set(v___x_23_, 2, v_x_14_);
lean_ctor_set(v___x_23_, 1, v_x_13_);
v___x_31_ = v___x_23_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_32_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_lchild_18_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_x_13_);
lean_ctor_set(v_reuseFailAlloc_32_, 2, v_x_14_);
lean_ctor_set(v_reuseFailAlloc_32_, 3, v_rchild_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_32_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
v___x_31_ = v_reuseFailAlloc_32_;
state = 3; continue;
}
}
_ => {
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); 
v___x_33_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg(v_rchild_21_, v_x_13_, v_x_14_);
if v_isShared_24_ == 0 {
lean_ctor_set(v___x_23_, 3, v___x_33_);
v___x_35_ = v___x_23_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_36_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_lchild_18_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_key_19_);
lean_ctor_set(v_reuseFailAlloc_36_, 2, v_val_20_);
lean_ctor_set(v_reuseFailAlloc_36_, 3, v___x_33_);
lean_ctor_set_uint8(v_reuseFailAlloc_36_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
v___x_35_ = v_reuseFailAlloc_36_;
state = 4; continue;
}
}
}
}
5 => {
v___x_45_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg___lam__0(v_x_13_, v_key_39_);
match v___x_45_
{
0 => {
let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); 
v___x_46_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg(v_lchild_38_, v_x_13_, v_x_14_);
if lean_obj_tag(v___x_46_) == 1 {
let mut v_color_47_: u8 = 0; let mut v_lchild_48_: *mut lean_object = core::ptr::null_mut(); let mut v_key_49_: *mut lean_object = core::ptr::null_mut(); let mut v_val_50_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_51_: *mut lean_object = core::ptr::null_mut(); let mut v_a_53_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_54_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_55_: *mut lean_object = core::ptr::null_mut(); let mut v_b_56_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_57_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_58_: *mut lean_object = core::ptr::null_mut(); let mut v_c_59_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_60_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_61_: *mut lean_object = core::ptr::null_mut(); let mut v_d_62_: *mut lean_object = core::ptr::null_mut(); 
v_color_47_ = lean_ctor_get_uint8(v___x_46_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
v_lchild_48_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_lchild_48_);
v_key_49_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_key_49_);
v_val_50_ = lean_ctor_get(v___x_46_, 2);
lean_inc(v_val_50_);
v_rchild_51_ = lean_ctor_get(v___x_46_, 3);
lean_inc(v_rchild_51_);
if v_color_47_ == 0 {
if lean_obj_tag(v_lchild_48_) == 1 {
let mut v_color_68_: u8 = 0; 
v_color_68_ = lean_ctor_get_uint8(v_lchild_48_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_68_ == 0 {
let mut v_lchild_69_: *mut lean_object = core::ptr::null_mut(); let mut v_key_70_: *mut lean_object = core::ptr::null_mut(); let mut v_val_71_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_72_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_46_, 4);
v_lchild_69_ = lean_ctor_get(v_lchild_48_, 0);
lean_inc(v_lchild_69_);
v_key_70_ = lean_ctor_get(v_lchild_48_, 1);
lean_inc(v_key_70_);
v_val_71_ = lean_ctor_get(v_lchild_48_, 2);
lean_inc(v_val_71_);
v_rchild_72_ = lean_ctor_get(v_lchild_48_, 3);
lean_inc(v_rchild_72_);
lean_dec_ref_known(v_lchild_48_, 4);
v_a_53_ = v_lchild_69_;
v_kx_54_ = v_key_70_;
v_vx_55_ = v_val_71_;
v_b_56_ = v_rchild_72_;
v_ky_57_ = v_key_49_;
v_vy_58_ = v_val_50_;
v_c_59_ = v_rchild_51_;
v_kz_60_ = v_key_39_;
v_vz_61_ = v_val_40_;
v_d_62_ = v_rchild_41_;
state = 6; continue;
} else {
if lean_obj_tag(v_rchild_51_) == 1 {
let mut v_color_73_: u8 = 0; 
v_color_73_ = lean_ctor_get_uint8(v_rchild_51_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_73_ == 0 {
let mut v_lchild_74_: *mut lean_object = core::ptr::null_mut(); let mut v_key_75_: *mut lean_object = core::ptr::null_mut(); let mut v_val_76_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_77_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_46_, 4);
v_lchild_74_ = lean_ctor_get(v_rchild_51_, 0);
lean_inc(v_lchild_74_);
v_key_75_ = lean_ctor_get(v_rchild_51_, 1);
lean_inc(v_key_75_);
v_val_76_ = lean_ctor_get(v_rchild_51_, 2);
lean_inc(v_val_76_);
v_rchild_77_ = lean_ctor_get(v_rchild_51_, 3);
lean_inc(v_rchild_77_);
lean_dec_ref_known(v_rchild_51_, 4);
v_a_53_ = v_lchild_48_;
v_kx_54_ = v_key_49_;
v_vx_55_ = v_val_50_;
v_b_56_ = v_lchild_74_;
v_ky_57_ = v_key_75_;
v_vy_58_ = v_val_76_;
v_c_59_ = v_rchild_77_;
v_kz_60_ = v_key_39_;
v_vz_61_ = v_val_40_;
v_d_62_ = v_rchild_41_;
state = 6; continue;
} else {
let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_80_: u8 = 0; let mut v_isSharedCheck_84_: u8 = 0; 
lean_dec_ref_known(v_lchild_48_, 4);
lean_dec(v_val_50_);
lean_dec(v_key_49_);
lean_del_object(v___x_43_);
v_isSharedCheck_84_ = (!lean_is_exclusive(v_rchild_51_)) as u8;
if v_isSharedCheck_84_ == 0 {
let mut v_unused_85_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_86_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_87_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_88_: *mut lean_object = core::ptr::null_mut(); 
v_unused_85_ = lean_ctor_get(v_rchild_51_, 3);
lean_dec(v_unused_85_);
v_unused_86_ = lean_ctor_get(v_rchild_51_, 2);
lean_dec(v_unused_86_);
v_unused_87_ = lean_ctor_get(v_rchild_51_, 1);
lean_dec(v_unused_87_);
v_unused_88_ = lean_ctor_get(v_rchild_51_, 0);
lean_dec(v_unused_88_);
v___x_79_ = v_rchild_51_;
v_isShared_80_ = v_isSharedCheck_84_;
state = 8; continue;
} else {
lean_dec(v_rchild_51_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
state = 8; continue;
}
}
} else {
let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_91_: u8 = 0; let mut v_isSharedCheck_95_: u8 = 0; 
lean_dec(v_rchild_51_);
lean_dec(v_val_50_);
lean_dec(v_key_49_);
lean_del_object(v___x_43_);
v_isSharedCheck_95_ = (!lean_is_exclusive(v_lchild_48_)) as u8;
if v_isSharedCheck_95_ == 0 {
let mut v_unused_96_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_97_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_98_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_99_: *mut lean_object = core::ptr::null_mut(); 
v_unused_96_ = lean_ctor_get(v_lchild_48_, 3);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_lchild_48_, 2);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_lchild_48_, 1);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_lchild_48_, 0);
lean_dec(v_unused_99_);
v___x_90_ = v_lchild_48_;
v_isShared_91_ = v_isSharedCheck_95_;
state = 10; continue;
} else {
lean_dec(v_lchild_48_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
state = 10; continue;
}
}
}
} else {
if lean_obj_tag(v_rchild_51_) == 1 {
let mut v_color_100_: u8 = 0; 
v_color_100_ = lean_ctor_get_uint8(v_rchild_51_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_100_ == 0 {
let mut v_lchild_101_: *mut lean_object = core::ptr::null_mut(); let mut v_key_102_: *mut lean_object = core::ptr::null_mut(); let mut v_val_103_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_104_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_46_, 4);
v_lchild_101_ = lean_ctor_get(v_rchild_51_, 0);
lean_inc(v_lchild_101_);
v_key_102_ = lean_ctor_get(v_rchild_51_, 1);
lean_inc(v_key_102_);
v_val_103_ = lean_ctor_get(v_rchild_51_, 2);
lean_inc(v_val_103_);
v_rchild_104_ = lean_ctor_get(v_rchild_51_, 3);
lean_inc(v_rchild_104_);
lean_dec_ref_known(v_rchild_51_, 4);
v_a_53_ = v_lchild_48_;
v_kx_54_ = v_key_49_;
v_vx_55_ = v_val_50_;
v_b_56_ = v_lchild_101_;
v_ky_57_ = v_key_102_;
v_vy_58_ = v_val_103_;
v_c_59_ = v_rchild_104_;
v_kz_60_ = v_key_39_;
v_vz_61_ = v_val_40_;
v_d_62_ = v_rchild_41_;
state = 6; continue;
} else {
let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_107_: u8 = 0; let mut v_isSharedCheck_111_: u8 = 0; 
lean_dec(v_val_50_);
lean_dec(v_key_49_);
lean_dec(v_lchild_48_);
lean_del_object(v___x_43_);
v_isSharedCheck_111_ = (!lean_is_exclusive(v_rchild_51_)) as u8;
if v_isSharedCheck_111_ == 0 {
let mut v_unused_112_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_113_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_114_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_115_: *mut lean_object = core::ptr::null_mut(); 
v_unused_112_ = lean_ctor_get(v_rchild_51_, 3);
lean_dec(v_unused_112_);
v_unused_113_ = lean_ctor_get(v_rchild_51_, 2);
lean_dec(v_unused_113_);
v_unused_114_ = lean_ctor_get(v_rchild_51_, 1);
lean_dec(v_unused_114_);
v_unused_115_ = lean_ctor_get(v_rchild_51_, 0);
lean_dec(v_unused_115_);
v___x_106_ = v_rchild_51_;
v_isShared_107_ = v_isSharedCheck_111_;
state = 12; continue;
} else {
lean_dec(v_rchild_51_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
state = 12; continue;
}
}
} else {
let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_51_);
lean_dec(v_val_50_);
lean_dec(v_key_49_);
lean_dec(v_lchild_48_);
lean_del_object(v___x_43_);
v___x_116_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_116_, 0, v___x_46_);
lean_ctor_set(v___x_116_, 1, v_key_39_);
lean_ctor_set(v___x_116_, 2, v_val_40_);
lean_ctor_set(v___x_116_, 3, v_rchild_41_);
lean_ctor_set_uint8(v___x_116_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
return v___x_116_;
}
}
} else {
let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_51_);
lean_dec(v_val_50_);
lean_dec(v_key_49_);
lean_dec(v_lchild_48_);
lean_del_object(v___x_43_);
v___x_117_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_117_, 0, v___x_46_);
lean_ctor_set(v___x_117_, 1, v_key_39_);
lean_ctor_set(v___x_117_, 2, v_val_40_);
lean_ctor_set(v___x_117_, 3, v_rchild_41_);
lean_ctor_set_uint8(v___x_117_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
return v___x_117_;
}
} else {
let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_44_ == 0 {
lean_ctor_set(v___x_43_, 0, v___x_46_);
v___x_119_ = v___x_43_;
state = 14; continue;
} else {
let mut v_reuseFailAlloc_120_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_key_39_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_val_40_);
lean_ctor_set(v_reuseFailAlloc_120_, 3, v_rchild_41_);
lean_ctor_set_uint8(v_reuseFailAlloc_120_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
v___x_119_ = v_reuseFailAlloc_120_;
state = 14; continue;
}
}
}
1 => {
let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_val_40_);
lean_dec(v_key_39_);
if v_isShared_44_ == 0 {
lean_ctor_set(v___x_43_, 2, v_x_14_);
lean_ctor_set(v___x_43_, 1, v_x_13_);
v___x_122_ = v___x_43_;
state = 15; continue;
} else {
let mut v_reuseFailAlloc_123_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_lchild_38_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_x_13_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_x_14_);
lean_ctor_set(v_reuseFailAlloc_123_, 3, v_rchild_41_);
lean_ctor_set_uint8(v_reuseFailAlloc_123_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
v___x_122_ = v_reuseFailAlloc_123_;
state = 15; continue;
}
}
_ => {
let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); 
v___x_124_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg(v_rchild_41_, v_x_13_, v_x_14_);
if lean_obj_tag(v___x_124_) == 1 {
let mut v_color_125_: u8 = 0; let mut v_lchild_126_: *mut lean_object = core::ptr::null_mut(); let mut v_key_127_: *mut lean_object = core::ptr::null_mut(); let mut v_val_128_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_129_: *mut lean_object = core::ptr::null_mut(); let mut v_a_131_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_132_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_133_: *mut lean_object = core::ptr::null_mut(); let mut v_b_134_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_135_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_136_: *mut lean_object = core::ptr::null_mut(); let mut v_c_137_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_138_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_139_: *mut lean_object = core::ptr::null_mut(); let mut v_d_140_: *mut lean_object = core::ptr::null_mut(); 
v_color_125_ = lean_ctor_get_uint8(v___x_124_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
v_lchild_126_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_lchild_126_);
v_key_127_ = lean_ctor_get(v___x_124_, 1);
lean_inc(v_key_127_);
v_val_128_ = lean_ctor_get(v___x_124_, 2);
lean_inc(v_val_128_);
v_rchild_129_ = lean_ctor_get(v___x_124_, 3);
lean_inc(v_rchild_129_);
if v_color_125_ == 0 {
if lean_obj_tag(v_lchild_126_) == 1 {
let mut v_color_146_: u8 = 0; 
v_color_146_ = lean_ctor_get_uint8(v_lchild_126_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_146_ == 0 {
let mut v_lchild_147_: *mut lean_object = core::ptr::null_mut(); let mut v_key_148_: *mut lean_object = core::ptr::null_mut(); let mut v_val_149_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_150_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_124_, 4);
v_lchild_147_ = lean_ctor_get(v_lchild_126_, 0);
lean_inc(v_lchild_147_);
v_key_148_ = lean_ctor_get(v_lchild_126_, 1);
lean_inc(v_key_148_);
v_val_149_ = lean_ctor_get(v_lchild_126_, 2);
lean_inc(v_val_149_);
v_rchild_150_ = lean_ctor_get(v_lchild_126_, 3);
lean_inc(v_rchild_150_);
lean_dec_ref_known(v_lchild_126_, 4);
v_a_131_ = v_lchild_38_;
v_kx_132_ = v_key_39_;
v_vx_133_ = v_val_40_;
v_b_134_ = v_lchild_147_;
v_ky_135_ = v_key_148_;
v_vy_136_ = v_val_149_;
v_c_137_ = v_rchild_150_;
v_kz_138_ = v_key_127_;
v_vz_139_ = v_val_128_;
v_d_140_ = v_rchild_129_;
state = 16; continue;
} else {
if lean_obj_tag(v_rchild_129_) == 1 {
let mut v_color_151_: u8 = 0; 
v_color_151_ = lean_ctor_get_uint8(v_rchild_129_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_151_ == 0 {
let mut v_lchild_152_: *mut lean_object = core::ptr::null_mut(); let mut v_key_153_: *mut lean_object = core::ptr::null_mut(); let mut v_val_154_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_155_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_124_, 4);
v_lchild_152_ = lean_ctor_get(v_rchild_129_, 0);
lean_inc(v_lchild_152_);
v_key_153_ = lean_ctor_get(v_rchild_129_, 1);
lean_inc(v_key_153_);
v_val_154_ = lean_ctor_get(v_rchild_129_, 2);
lean_inc(v_val_154_);
v_rchild_155_ = lean_ctor_get(v_rchild_129_, 3);
lean_inc(v_rchild_155_);
lean_dec_ref_known(v_rchild_129_, 4);
v_a_131_ = v_lchild_38_;
v_kx_132_ = v_key_39_;
v_vx_133_ = v_val_40_;
v_b_134_ = v_lchild_126_;
v_ky_135_ = v_key_127_;
v_vy_136_ = v_val_128_;
v_c_137_ = v_lchild_152_;
v_kz_138_ = v_key_153_;
v_vz_139_ = v_val_154_;
v_d_140_ = v_rchild_155_;
state = 16; continue;
} else {
let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_158_: u8 = 0; let mut v_isSharedCheck_162_: u8 = 0; 
lean_dec_ref_known(v_lchild_126_, 4);
lean_dec(v_val_128_);
lean_dec(v_key_127_);
lean_del_object(v___x_43_);
v_isSharedCheck_162_ = (!lean_is_exclusive(v_rchild_129_)) as u8;
if v_isSharedCheck_162_ == 0 {
let mut v_unused_163_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_164_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_165_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_166_: *mut lean_object = core::ptr::null_mut(); 
v_unused_163_ = lean_ctor_get(v_rchild_129_, 3);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_rchild_129_, 2);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_rchild_129_, 1);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_rchild_129_, 0);
lean_dec(v_unused_166_);
v___x_157_ = v_rchild_129_;
v_isShared_158_ = v_isSharedCheck_162_;
state = 18; continue;
} else {
lean_dec(v_rchild_129_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
state = 18; continue;
}
}
} else {
let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_169_: u8 = 0; let mut v_isSharedCheck_173_: u8 = 0; 
lean_dec(v_rchild_129_);
lean_dec(v_val_128_);
lean_dec(v_key_127_);
lean_del_object(v___x_43_);
v_isSharedCheck_173_ = (!lean_is_exclusive(v_lchild_126_)) as u8;
if v_isSharedCheck_173_ == 0 {
let mut v_unused_174_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_175_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_176_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_177_: *mut lean_object = core::ptr::null_mut(); 
v_unused_174_ = lean_ctor_get(v_lchild_126_, 3);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_lchild_126_, 2);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_lchild_126_, 1);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_lchild_126_, 0);
lean_dec(v_unused_177_);
v___x_168_ = v_lchild_126_;
v_isShared_169_ = v_isSharedCheck_173_;
state = 20; continue;
} else {
lean_dec(v_lchild_126_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
state = 20; continue;
}
}
}
} else {
if lean_obj_tag(v_rchild_129_) == 1 {
let mut v_color_178_: u8 = 0; 
v_color_178_ = lean_ctor_get_uint8(v_rchild_129_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_178_ == 0 {
let mut v_lchild_179_: *mut lean_object = core::ptr::null_mut(); let mut v_key_180_: *mut lean_object = core::ptr::null_mut(); let mut v_val_181_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_182_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_124_, 4);
v_lchild_179_ = lean_ctor_get(v_rchild_129_, 0);
lean_inc(v_lchild_179_);
v_key_180_ = lean_ctor_get(v_rchild_129_, 1);
lean_inc(v_key_180_);
v_val_181_ = lean_ctor_get(v_rchild_129_, 2);
lean_inc(v_val_181_);
v_rchild_182_ = lean_ctor_get(v_rchild_129_, 3);
lean_inc(v_rchild_182_);
lean_dec_ref_known(v_rchild_129_, 4);
v_a_131_ = v_lchild_38_;
v_kx_132_ = v_key_39_;
v_vx_133_ = v_val_40_;
v_b_134_ = v_lchild_126_;
v_ky_135_ = v_key_127_;
v_vy_136_ = v_val_128_;
v_c_137_ = v_lchild_179_;
v_kz_138_ = v_key_180_;
v_vz_139_ = v_val_181_;
v_d_140_ = v_rchild_182_;
state = 16; continue;
} else {
let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_185_: u8 = 0; let mut v_isSharedCheck_189_: u8 = 0; 
lean_dec(v_val_128_);
lean_dec(v_key_127_);
lean_dec(v_lchild_126_);
lean_del_object(v___x_43_);
v_isSharedCheck_189_ = (!lean_is_exclusive(v_rchild_129_)) as u8;
if v_isSharedCheck_189_ == 0 {
let mut v_unused_190_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_191_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_192_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_193_: *mut lean_object = core::ptr::null_mut(); 
v_unused_190_ = lean_ctor_get(v_rchild_129_, 3);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_rchild_129_, 2);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_rchild_129_, 1);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_rchild_129_, 0);
lean_dec(v_unused_193_);
v___x_184_ = v_rchild_129_;
v_isShared_185_ = v_isSharedCheck_189_;
state = 22; continue;
} else {
lean_dec(v_rchild_129_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
state = 22; continue;
}
}
} else {
let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_129_);
lean_dec(v_val_128_);
lean_dec(v_key_127_);
lean_dec(v_lchild_126_);
lean_del_object(v___x_43_);
v___x_194_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_194_, 0, v_lchild_38_);
lean_ctor_set(v___x_194_, 1, v_key_39_);
lean_ctor_set(v___x_194_, 2, v_val_40_);
lean_ctor_set(v___x_194_, 3, v___x_124_);
lean_ctor_set_uint8(v___x_194_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
return v___x_194_;
}
}
} else {
let mut v___x_195_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_129_);
lean_dec(v_val_128_);
lean_dec(v_key_127_);
lean_dec(v_lchild_126_);
lean_del_object(v___x_43_);
v___x_195_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_195_, 0, v_lchild_38_);
lean_ctor_set(v___x_195_, 1, v_key_39_);
lean_ctor_set(v___x_195_, 2, v_val_40_);
lean_ctor_set(v___x_195_, 3, v___x_124_);
lean_ctor_set_uint8(v___x_195_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
return v___x_195_;
}
} else {
let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_44_ == 0 {
lean_ctor_set(v___x_43_, 3, v___x_124_);
v___x_197_ = v___x_43_;
state = 24; continue;
} else {
let mut v_reuseFailAlloc_198_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_lchild_38_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_key_39_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_val_40_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v___x_124_);
lean_ctor_set_uint8(v_reuseFailAlloc_198_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_17_);
v___x_197_ = v_reuseFailAlloc_198_;
state = 24; continue;
}
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_insert___at___00mkMapAux_spec__0___redArg(mut v_t_200_: *mut lean_object, mut v_k_201_: *mut lean_object, mut v_v_202_: *mut lean_object) -> *mut lean_object{
let mut v___x_203_: u8 = 0; 
v___x_203_ = l_Lean_RBNode_isRed___redArg(v_t_200_);
if v___x_203_ == 0 {
let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); 
v___x_204_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg(v_t_200_, v_k_201_, v_v_202_);
return v___x_204_;
} else {
let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); 
v___x_205_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg(v_t_200_, v_k_201_, v_v_202_);
v___x_206_ = l_Lean_RBNode_setBlack___redArg(v___x_205_);
return v___x_206_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_mkMapAux(mut v_x_207_: *mut lean_object, mut v_x_208_: *mut lean_object) -> *mut lean_object{
let mut v_zero_209_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_210_: u8 = 0; let mut v_one_211_: *mut lean_object = core::ptr::null_mut(); let mut v_n_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: u8 = 0; let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_209_ = lean_unsigned_to_nat(0);
v_isZero_210_ = lean_nat_dec_eq(v_x_207_, v_zero_209_);
if v_isZero_210_ == 1 {
lean_dec(v_x_207_);
return v_x_208_;
} else {
let mut v_one_211_: *mut lean_object = core::ptr::null_mut(); let mut v_n_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: u8 = 0; let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); 
v_one_211_ = lean_unsigned_to_nat(1);
v_n_212_ = lean_nat_sub(v_x_207_, v_one_211_);
lean_dec(v_x_207_);
v___x_213_ = lean_unsigned_to_nat(10);
v___x_214_ = lean_nat_mod(v_n_212_, v___x_213_);
v___x_215_ = lean_nat_dec_eq(v___x_214_, v_zero_209_);
lean_dec(v___x_214_);
v___x_216_ = lean_box((v___x_215_) as usize);
lean_inc(v_n_212_);
v___x_217_ = l_Lean_RBNode_insert___at___00mkMapAux_spec__0___redArg(v_x_208_, v_n_212_, v___x_216_);
v_x_207_ = v_n_212_;
v_x_208_ = v___x_217_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_insert___at___00mkMapAux_spec__0(mut v_00_u03b2_219_: *mut lean_object, mut v_t_220_: *mut lean_object, mut v_k_221_: *mut lean_object, mut v_v_222_: *mut lean_object) -> *mut lean_object{
let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); 
v___x_223_ = l_Lean_RBNode_insert___at___00mkMapAux_spec__0___redArg(v_t_220_, v_k_221_, v_v_222_);
return v___x_223_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0(mut v_00_u03b2_224_: *mut lean_object, mut v_x_225_: *mut lean_object, mut v_x_226_: *mut lean_object, mut v_x_227_: *mut lean_object) -> *mut lean_object{
let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); 
v___x_228_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00mkMapAux_spec__0_spec__0___redArg(v_x_225_, v_x_226_, v_x_227_);
return v___x_228_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkMap(mut v_n_229_: *mut lean_object) -> *mut lean_object{
let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); 
v___x_230_ = lean_box(0);
v___x_231_ = l_mkMapAux(v_n_229_, v___x_230_);
return v___x_231_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_fold___at___00main_spec__0(mut v_x_232_: *mut lean_object, mut v_x_233_: *mut lean_object) -> *mut lean_object{
let mut v_val_234_: *mut lean_object = core::ptr::null_mut(); let mut v___x_235_: u8 = 0; let mut v_key_236_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_237_: *mut lean_object = core::ptr::null_mut(); let mut v_key_239_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_241_: *mut lean_object = core::ptr::null_mut(); let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_233_) == 0 {
return v_x_232_;
} else {
let mut v_val_234_: *mut lean_object = core::ptr::null_mut(); let mut v___x_235_: u8 = 0; 
lean_dec(v_x_232_);
v_val_234_ = lean_ctor_get(v_x_233_, 2);
v___x_235_ = (lean_unbox(v_val_234_) as u8);
if v___x_235_ == 0 {
let mut v_key_236_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_237_: *mut lean_object = core::ptr::null_mut(); 
v_key_236_ = lean_ctor_get(v_x_233_, 1);
lean_inc(v_key_236_);
v_rchild_237_ = lean_ctor_get(v_x_233_, 3);
lean_inc(v_rchild_237_);
lean_dec_ref_known(v_x_233_, 4);
v_x_232_ = v_key_236_;
v_x_233_ = v_rchild_237_;
state = 0; continue;
} else {
let mut v_key_239_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_241_: *mut lean_object = core::ptr::null_mut(); let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); 
v_key_239_ = lean_ctor_get(v_x_233_, 1);
lean_inc(v_key_239_);
v_rchild_240_ = lean_ctor_get(v_x_233_, 3);
lean_inc(v_rchild_240_);
lean_dec_ref_known(v_x_233_, 4);
v___x_241_ = lean_unsigned_to_nat(1);
v___x_242_ = lean_nat_add(v_key_239_, v___x_241_);
lean_dec(v_key_239_);
v_x_232_ = v___x_242_;
v_x_233_ = v_rchild_240_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(mut v_s_244_: *mut lean_object) -> *mut lean_object{
let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); 
v___x_246_ = lean_get_stdout();
v_putStr_247_ = lean_ctor_get(v___x_246_, 4);
lean_inc_ref(v_putStr_247_);
lean_dec_ref(v___x_246_);
v___x_248_ = lean_apply_2(v_putStr_247_, v_s_244_, lean_box(0));
return v___x_248_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__1___boxed(mut v_s_249_: *mut lean_object, mut v_a_250_: *mut lean_object) -> *mut lean_object{
let mut v_res_251_: *mut lean_object = core::ptr::null_mut(); 
v_res_251_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(v_s_249_);
return v_res_251_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_252_: *mut lean_object) -> *mut lean_object{
let mut v___x_254_: u32 = 0; let mut v___x_255_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); 
v___x_254_ = 10;
v___x_255_ = lean_string_push(v_s_252_, v___x_254_);
v___x_256_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(v___x_255_);
return v___x_256_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_257_: *mut lean_object, mut v_a_258_: *mut lean_object) -> *mut lean_object{
let mut v_res_259_: *mut lean_object = core::ptr::null_mut(); 
v_res_259_ = l_IO_println___at___00main_spec__1(v_s_257_);
return v_res_259_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_261_: *mut lean_object) -> *mut lean_object{
let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); let mut v_m_269_: *mut lean_object = core::ptr::null_mut(); let mut v_v_270_: *mut lean_object = core::ptr::null_mut(); let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); 
v___x_263_ = l_main___closed__0;
v___x_264_ = l_List_head_x21___redArg(v___x_263_, v_xs_261_);
lean_dec(v_xs_261_);
v___x_265_ = lean_unsigned_to_nat(0);
v___x_266_ = lean_string_utf8_byte_size(v___x_264_);
v___x_267_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_267_, 0, v___x_264_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
v___x_268_ = l_String_Slice_toNat_x21(v___x_267_);
lean_dec_ref_known(v___x_267_, 3);
v_m_269_ = l_mkMap(v___x_268_);
v_v_270_ = l_Lean_RBNode_fold___at___00main_spec__0(v___x_265_, v_m_269_);
v___x_271_ = l_Nat_reprFast(v_v_270_);
v___x_272_ = l_IO_println___at___00main_spec__1(v___x_271_);
return v___x_272_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_273_: *mut lean_object, mut v_a_274_: *mut lean_object) -> *mut lean_object{
let mut v_res_275_: *mut lean_object = core::ptr::null_mut(); 
v_res_275_ = _lean_main(v_xs_273_);
return v_res_275_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_RBMap(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_rbmap__library(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin);
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
  lean_initialize();
  let res = initialize_rbmap__library(1 /* builtin */);
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
