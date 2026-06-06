// Lean compiler output
// Module: «binarytrees.st»
// Imports: public import Init public meta import Init public import Std.Data.Iterators.Producers.Range public import Std.Data.Iterators.Combinators.StepSize
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_uint32_dec_eq(_: u32, _: u32) -> u8;
    fn lean_uint32_sub(_: u32, _: u32) -> u32;
    fn lean_uint32_add(_: u32, _: u32) -> u32;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_pow(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_of_nat(_: *mut lean_object) -> u32;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_to_nat(_: u32) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static mut l_instInhabitedTree: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_make_x27___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_make_x27___closed__0: *mut lean_object = core::ptr::addr_of!(l_make_x27___closed__0_value) as *mut lean_object;
#[no_mangle] pub static mut l_minN: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_out___closed__0_value: lean_string_object<11> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [32, 111, 102, 32, 100, 101, 112, 116, 104, 32, 0]};
static mut l_out___closed__0: *mut lean_object = core::ptr::addr_of!(l_out___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_out___closed__1_value: lean_string_object<10> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [9, 32, 99, 104, 101, 99, 107, 58, 32, 0]};
static mut l_out___closed__1: *mut lean_object = core::ptr::addr_of!(l_out___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg___closed__0_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [9, 32, 116, 114, 101, 101, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<13> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 116, 114, 101, 116, 99, 104, 32, 116, 114, 101, 101, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 4 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_string_object<16> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [108, 111, 110, 103, 32, 108, 105, 118, 101, 100, 32, 116, 114, 101, 101, 0]};
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_main___boxed__const__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorIdx(mut v_x_1_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_1_) == 0 {
let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); 
v___x_2_ = lean_unsigned_to_nat(0);
return v___x_2_;
} else {
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_unsigned_to_nat(1);
return v___x_3_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorIdx___boxed(mut v_x_4_: *mut lean_object) -> *mut lean_object{
let mut v_res_5_: *mut lean_object = core::ptr::null_mut(); 
v_res_5_ = l_Tree_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorElim___redArg(mut v_t_6_: *mut lean_object, mut v_k_7_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_t_6_) == 0 {
return v_k_7_;
} else {
let mut v_l_8_: *mut lean_object = core::ptr::null_mut(); let mut v_r_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); 
v_l_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_l_8_);
v_r_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_r_9_);
lean_dec_ref_known(v_t_6_, 2);
v___x_10_ = lean_apply_2(v_k_7_, v_l_8_, v_r_9_);
return v___x_10_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorElim(mut v_motive_11_: *mut lean_object, mut v_ctorIdx_12_: *mut lean_object, mut v_t_13_: *mut lean_object, mut v_h_14_: *mut lean_object, mut v_k_15_: *mut lean_object) -> *mut lean_object{
let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); 
v___x_16_ = l_Tree_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_ctorElim___boxed(mut v_motive_17_: *mut lean_object, mut v_ctorIdx_18_: *mut lean_object, mut v_t_19_: *mut lean_object, mut v_h_20_: *mut lean_object, mut v_k_21_: *mut lean_object) -> *mut lean_object{
let mut v_res_22_: *mut lean_object = core::ptr::null_mut(); 
v_res_22_ = l_Tree_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_nil_elim___redArg(mut v_t_23_: *mut lean_object, mut v_nil_24_: *mut lean_object) -> *mut lean_object{
let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); 
v___x_25_ = l_Tree_ctorElim___redArg(v_t_23_, v_nil_24_);
return v___x_25_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_nil_elim(mut v_motive_26_: *mut lean_object, mut v_t_27_: *mut lean_object, mut v_h_28_: *mut lean_object, mut v_nil_29_: *mut lean_object) -> *mut lean_object{
let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); 
v___x_30_ = l_Tree_ctorElim___redArg(v_t_27_, v_nil_29_);
return v___x_30_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_node_elim___redArg(mut v_t_31_: *mut lean_object, mut v_node_32_: *mut lean_object) -> *mut lean_object{
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); 
v___x_33_ = l_Tree_ctorElim___redArg(v_t_31_, v_node_32_);
return v___x_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_Tree_node_elim(mut v_motive_34_: *mut lean_object, mut v_t_35_: *mut lean_object, mut v_h_36_: *mut lean_object, mut v_node_37_: *mut lean_object) -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); 
v___x_38_ = l_Tree_ctorElim___redArg(v_t_35_, v_node_37_);
return v___x_38_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_instInhabitedTree() -> *mut lean_object{
let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); 
v___x_39_ = lean_box(0);
return v___x_39_;
}
#[no_mangle] pub unsafe extern "C" fn l_make_x27(mut v_n_42_: u32, mut v_d_43_: u32) -> *mut lean_object{
let mut v___x_44_: u32 = 0; let mut v___x_45_: u8 = 0; 
v___x_44_ = 0;
v___x_45_ = lean_uint32_dec_eq(v_d_43_, v___x_44_);
if v___x_45_ == 0 {
let mut v___x_46_: u32 = 0; let mut v___x_47_: u32 = 0; let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: u32 = 0; let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
v___x_46_ = 1;
v___x_47_ = lean_uint32_sub(v_d_43_, v___x_46_);
v___x_48_ = l_make_x27(v_n_42_, v___x_47_);
v___x_49_ = lean_uint32_add(v_n_42_, v___x_46_);
v___x_50_ = l_make_x27(v___x_49_, v___x_47_);
v___x_51_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_51_, 0, v___x_48_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
} else {
let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); 
v___x_52_ = l_make_x27___closed__0;
return v___x_52_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_make_x27___boxed(mut v_n_53_: *mut lean_object, mut v_d_54_: *mut lean_object) -> *mut lean_object{
let mut v_n_boxed_55_: u32 = 0; let mut v_d_boxed_56_: u32 = 0; let mut v_res_57_: *mut lean_object = core::ptr::null_mut(); 
v_n_boxed_55_ = lean_unbox_uint32(v_n_53_);
lean_dec(v_n_53_);
v_d_boxed_56_ = lean_unbox_uint32(v_d_54_);
lean_dec(v_d_54_);
v_res_57_ = l_make_x27(v_n_boxed_55_, v_d_boxed_56_);
return v_res_57_;
}
#[no_mangle] pub unsafe extern "C" fn l_make(mut v_d_58_: u32) -> *mut lean_object{
let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); 
v___x_59_ = l_make_x27(v_d_58_, v_d_58_);
return v___x_59_;
}
#[no_mangle] pub unsafe extern "C" fn l_make___boxed(mut v_d_60_: *mut lean_object) -> *mut lean_object{
let mut v_d_boxed_61_: u32 = 0; let mut v_res_62_: *mut lean_object = core::ptr::null_mut(); 
v_d_boxed_61_ = lean_unbox_uint32(v_d_60_);
lean_dec(v_d_60_);
v_res_62_ = l_make(v_d_boxed_61_);
return v_res_62_;
}
#[no_mangle] pub unsafe extern "C" fn l_check(mut v_x_63_: *mut lean_object) -> u32{
if lean_obj_tag(v_x_63_) == 0 {
let mut v___x_64_: u32 = 0; 
v___x_64_ = 0;
return v___x_64_;
} else {
let mut v_l_65_: *mut lean_object = core::ptr::null_mut(); let mut v_r_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: u32 = 0; let mut v___x_68_: u32 = 0; let mut v___x_69_: u32 = 0; let mut v___x_70_: u32 = 0; let mut v___x_71_: u32 = 0; 
v_l_65_ = lean_ctor_get(v_x_63_, 0);
v_r_66_ = lean_ctor_get(v_x_63_, 1);
v___x_67_ = 1;
v___x_68_ = l_check(v_l_65_);
v___x_69_ = lean_uint32_add(v___x_67_, v___x_68_);
v___x_70_ = l_check(v_r_66_);
v___x_71_ = lean_uint32_add(v___x_69_, v___x_70_);
return v___x_71_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_check___boxed(mut v_x_72_: *mut lean_object) -> *mut lean_object{
let mut v_res_73_: u32 = 0; let mut v_r_74_: *mut lean_object = core::ptr::null_mut(); 
v_res_73_ = l_check(v_x_72_);
lean_dec(v_x_72_);
v_r_74_ = lean_box_uint32(v_res_73_);
return v_r_74_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_minN() -> *mut lean_object{
let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); 
v___x_75_ = lean_unsigned_to_nat(4);
return v___x_75_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00out_spec__0_spec__0(mut v_s_76_: *mut lean_object) -> *mut lean_object{
let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); 
v___x_78_ = lean_get_stdout();
v_putStr_79_ = lean_ctor_get(v___x_78_, 4);
lean_inc_ref(v_putStr_79_);
lean_dec_ref(v___x_78_);
v___x_80_ = lean_apply_2(v_putStr_79_, v_s_76_, lean_box(0));
return v___x_80_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00out_spec__0_spec__0___boxed(mut v_s_81_: *mut lean_object, mut v_a_82_: *mut lean_object) -> *mut lean_object{
let mut v_res_83_: *mut lean_object = core::ptr::null_mut(); 
v_res_83_ = l_IO_print___at___00IO_println___at___00out_spec__0_spec__0(v_s_81_);
return v_res_83_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00out_spec__0(mut v_s_84_: *mut lean_object) -> *mut lean_object{
let mut v___x_86_: u32 = 0; let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); 
v___x_86_ = 10;
v___x_87_ = lean_string_push(v_s_84_, v___x_86_);
v___x_88_ = l_IO_print___at___00IO_println___at___00out_spec__0_spec__0(v___x_87_);
return v___x_88_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00out_spec__0___boxed(mut v_s_89_: *mut lean_object, mut v_a_90_: *mut lean_object) -> *mut lean_object{
let mut v_res_91_: *mut lean_object = core::ptr::null_mut(); 
v_res_91_ = l_IO_println___at___00out_spec__0(v_s_89_);
return v_res_91_;
}
#[no_mangle] pub unsafe extern "C" fn l_out(mut v_s_94_: *mut lean_object, mut v_n_95_: *mut lean_object, mut v_t_96_: u32) -> *mut lean_object{
let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); 
v___x_98_ = l_out___closed__0;
v___x_99_ = lean_string_append(v_s_94_, v___x_98_);
v___x_100_ = l_Nat_reprFast(v_n_95_);
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
lean_dec_ref(v___x_100_);
v___x_102_ = l_out___closed__1;
v___x_103_ = lean_string_append(v___x_101_, v___x_102_);
v___x_104_ = lean_uint32_to_nat(v_t_96_);
v___x_105_ = l_Nat_reprFast(v___x_104_);
v___x_106_ = lean_string_append(v___x_103_, v___x_105_);
lean_dec_ref(v___x_105_);
v___x_107_ = l_IO_println___at___00out_spec__0(v___x_106_);
return v___x_107_;
}
#[no_mangle] pub unsafe extern "C" fn l_out___boxed(mut v_s_108_: *mut lean_object, mut v_n_109_: *mut lean_object, mut v_t_110_: *mut lean_object, mut v_a_111_: *mut lean_object) -> *mut lean_object{
let mut v_t_boxed_112_: u32 = 0; let mut v_res_113_: *mut lean_object = core::ptr::null_mut(); 
v_t_boxed_112_ = lean_unbox_uint32(v_t_110_);
lean_dec(v_t_110_);
v_res_113_ = l_out(v_s_108_, v_n_109_, v_t_boxed_112_);
return v_res_113_;
}
#[no_mangle] pub unsafe extern "C" fn l_sumT(mut v_d_114_: u32, mut v_i_115_: u32, mut v_t_116_: u32) -> u32{
let mut v___x_117_: u32 = 0; let mut v___x_118_: u8 = 0; let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v_a_120_: u32 = 0; let mut v___x_121_: u32 = 0; let mut v___x_122_: u32 = 0; let mut v___x_123_: u32 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_117_ = 0;
v___x_118_ = lean_uint32_dec_eq(v_i_115_, v___x_117_);
if v___x_118_ == 0 {
let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v_a_120_: u32 = 0; let mut v___x_121_: u32 = 0; let mut v___x_122_: u32 = 0; let mut v___x_123_: u32 = 0; 
v___x_119_ = l_make_x27(v_d_114_, v_d_114_);
v_a_120_ = l_check(v___x_119_);
lean_dec(v___x_119_);
v___x_121_ = 1;
v___x_122_ = lean_uint32_sub(v_i_115_, v___x_121_);
v___x_123_ = lean_uint32_add(v_t_116_, v_a_120_);
v_i_115_ = v___x_122_;
v_t_116_ = v___x_123_;
state = 0; continue;
} else {
return v_t_116_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_sumT___boxed(mut v_d_125_: *mut lean_object, mut v_i_126_: *mut lean_object, mut v_t_127_: *mut lean_object) -> *mut lean_object{
let mut v_d_boxed_128_: u32 = 0; let mut v_i_boxed_129_: u32 = 0; let mut v_t_boxed_130_: u32 = 0; let mut v_res_131_: u32 = 0; let mut v_r_132_: *mut lean_object = core::ptr::null_mut(); 
v_d_boxed_128_ = lean_unbox_uint32(v_d_125_);
lean_dec(v_d_125_);
v_i_boxed_129_ = lean_unbox_uint32(v_i_126_);
lean_dec(v_i_126_);
v_t_boxed_130_ = lean_unbox_uint32(v_t_127_);
lean_dec(v_t_127_);
v_res_131_ = l_sumT(v_d_boxed_128_, v_i_boxed_129_, v_t_boxed_130_);
v_r_132_ = lean_box_uint32(v_res_131_);
return v_r_132_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(mut v___y_134_: *mut lean_object, mut v_a_135_: *mut lean_object, mut v_b_136_: *mut lean_object) -> *mut lean_object{
let mut v_inner_138_: *mut lean_object = core::ptr::null_mut(); let mut v_next_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v_nextIdx_141_: *mut lean_object = core::ptr::null_mut(); let mut v_n_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_145_: u8 = 0; let mut v_upperBound_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_149_: u8 = 0; let mut v_val_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_153_: u8 = 0; let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: u8 = 0; let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: u32 = 0; let mut v___x_171_: u32 = 0; let mut v___x_172_: u32 = 0; let mut v___x_173_: u32 = 0; let mut v___x_174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_180_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_181_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_182_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_183_: u8 = 0; let mut v_isSharedCheck_184_: u8 = 0; let mut v_unused_185_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_186_: u8 = 0; let mut v_unused_187_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_inner_138_ = lean_ctor_get(v_a_135_, 2);
lean_inc(v_inner_138_);
v_next_139_ = lean_ctor_get(v_inner_138_, 0);
lean_inc(v_next_139_);
if lean_obj_tag(v_next_139_) == 0 {
let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_inner_138_);
lean_dec_ref(v_a_135_);
v___x_140_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_140_, 0, v_b_136_);
return v___x_140_;
} else {
let mut v_nextIdx_141_: *mut lean_object = core::ptr::null_mut(); let mut v_n_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_145_: u8 = 0; let mut v_isSharedCheck_186_: u8 = 0; 
v_nextIdx_141_ = lean_ctor_get(v_a_135_, 0);
v_n_142_ = lean_ctor_get(v_a_135_, 1);
v_isSharedCheck_186_ = (!lean_is_exclusive(v_a_135_)) as u8;
if v_isSharedCheck_186_ == 0 {
let mut v_unused_187_: *mut lean_object = core::ptr::null_mut(); 
v_unused_187_ = lean_ctor_get(v_a_135_, 2);
lean_dec(v_unused_187_);
v___x_144_ = v_a_135_;
v_isShared_145_ = v_isSharedCheck_186_;
state = 1; continue;
} else {
lean_inc(v_n_142_);
lean_inc(v_nextIdx_141_);
lean_dec(v_a_135_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_186_;
state = 1; continue;
}
}
}
1 => {
v_upperBound_146_ = lean_ctor_get(v_inner_138_, 1);
v_isSharedCheck_184_ = (!lean_is_exclusive(v_inner_138_)) as u8;
if v_isSharedCheck_184_ == 0 {
let mut v_unused_185_: *mut lean_object = core::ptr::null_mut(); 
v_unused_185_ = lean_ctor_get(v_inner_138_, 0);
lean_dec(v_unused_185_);
v___x_148_ = v_inner_138_;
v_isShared_149_ = v_isSharedCheck_184_;
state = 2; continue;
} else {
lean_inc(v_upperBound_146_);
lean_dec(v_inner_138_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_184_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg___boxed(mut v___y_188_: *mut lean_object, mut v_a_189_: *mut lean_object, mut v_b_190_: *mut lean_object, mut v___y_191_: *mut lean_object) -> *mut lean_object{
let mut v_res_192_: *mut lean_object = core::ptr::null_mut(); 
v_res_192_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v___y_188_, v_a_189_, v_b_190_);
lean_dec(v___y_188_);
return v_res_192_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_197_: u32 = 0; let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); 
v___x_197_ = 1;
v___x_198_ = lean_box_uint32(v___x_197_);
return v___x_198_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__2() -> *mut lean_object{
let mut v___x_199_: u32 = 0; let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); 
v___x_199_ = 0;
v___x_200_ = lean_box_uint32(v___x_199_);
return v___x_200_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_x_201_: *mut lean_object) -> *mut lean_object{
let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_206_: *mut lean_object = core::ptr::null_mut(); let mut v_head_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_210_: u8 = 0; let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v_n_214_: *mut lean_object = core::ptr::null_mut(); let mut v___y_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v_stretchN_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: u32 = 0; let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v_c_221_: u32 = 0; let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_224_: u32 = 0; let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); let mut v___x_232_: *mut lean_object = core::ptr::null_mut(); let mut v___x_233_: u32 = 0; let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_237_: u8 = 0; let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v___x_240_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_241_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_242_: u8 = 0; let mut v_unused_243_: *mut lean_object = core::ptr::null_mut(); let mut v_a_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_247_: u8 = 0; let mut v___x_249_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_250_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_251_: u8 = 0; let mut v_a_252_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_255_: u8 = 0; let mut v___x_257_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_258_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_259_: u8 = 0; let mut v_reuseFailAlloc_260_: *mut lean_object = core::ptr::null_mut(); let mut v_a_261_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_264_: u8 = 0; let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_267_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_268_: u8 = 0; let mut v___x_269_: *mut lean_object = core::ptr::null_mut(); let mut v___x_270_: u8 = 0; let mut v_isSharedCheck_271_: u8 = 0; let mut v_unused_272_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_201_) == 1 {
let mut v_tail_206_: *mut lean_object = core::ptr::null_mut(); 
v_tail_206_ = lean_ctor_get(v_x_201_, 1);
if lean_obj_tag(v_tail_206_) == 0 {
let mut v_head_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_210_: u8 = 0; let mut v_isSharedCheck_271_: u8 = 0; 
v_head_207_ = lean_ctor_get(v_x_201_, 0);
v_isSharedCheck_271_ = (!lean_is_exclusive(v_x_201_)) as u8;
if v_isSharedCheck_271_ == 0 {
let mut v_unused_272_: *mut lean_object = core::ptr::null_mut(); 
v_unused_272_ = lean_ctor_get(v_x_201_, 1);
lean_dec(v_unused_272_);
v___x_209_ = v_x_201_;
v_isShared_210_ = v_isSharedCheck_271_;
state = 2; continue;
} else {
lean_inc(v_head_207_);
lean_dec(v_x_201_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_271_;
state = 2; continue;
}
} else {
lean_dec_ref_known(v_x_201_, 2);
state = 1; continue;
}
} else {
lean_dec(v_x_201_);
state = 1; continue;
}
}
1 => {
v___x_204_ = l_main___boxed__const__1;
v___x_205_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
2 => {
v___x_211_ = lean_unsigned_to_nat(0);
v___x_212_ = lean_string_utf8_byte_size(v_head_207_);
v___x_213_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_213_, 0, v_head_207_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
v_n_214_ = l_String_Slice_toNat_x21(v___x_213_);
lean_dec_ref_known(v___x_213_, 3);
v___x_269_ = lean_unsigned_to_nat(6);
v___x_270_ = lean_nat_dec_le(v___x_269_, v_n_214_);
if v___x_270_ == 0 {
lean_dec(v_n_214_);
v___y_216_ = v___x_269_;
state = 3; continue;
} else {
v___y_216_ = v_n_214_;
state = 3; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_x_273_: *mut lean_object, mut v_a_274_: *mut lean_object) -> *mut lean_object{
let mut v_res_275_: *mut lean_object = core::ptr::null_mut(); 
v_res_275_ = _lean_main(v_x_273_);
return v_res_275_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0(mut v___y_276_: *mut lean_object, mut v_inst_277_: *mut lean_object, mut v_R_278_: *mut lean_object, mut v_a_279_: *mut lean_object, mut v_b_280_: *mut lean_object, mut v_c_281_: *mut lean_object) -> *mut lean_object{
let mut v___x_283_: *mut lean_object = core::ptr::null_mut(); 
v___x_283_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v___y_276_, v_a_279_, v_b_280_);
return v___x_283_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___boxed(mut v___y_284_: *mut lean_object, mut v_inst_285_: *mut lean_object, mut v_R_286_: *mut lean_object, mut v_a_287_: *mut lean_object, mut v_b_288_: *mut lean_object, mut v_c_289_: *mut lean_object, mut v___y_290_: *mut lean_object) -> *mut lean_object{
let mut v_res_291_: *mut lean_object = core::ptr::null_mut(); 
v_res_291_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0(v___y_284_, v_inst_285_, v_R_286_, v_a_287_, v_b_288_, v_c_289_);
lean_dec(v___y_284_);
return v_res_291_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Data_Iterators_Producers_Range(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Data_Iterators_Combinators_StepSize(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_binarytrees_x2est(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Range(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_instInhabitedTree = _init_l_instInhabitedTree();
lean_mark_persistent(l_instInhabitedTree);
l_minN = _init_l_minN();
lean_mark_persistent(l_minN);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
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
  let res = initialize_binarytrees_x2est(1 /* builtin */);
  lean_io_mark_end_initialization();
  let mut ret_val = 1;
  if lean_io_result_is_ok(res) {
    lean_dec(res);
    lean_init_task_manager();
    let main_res = lean_run_main(run_main, argc, argv);
    lean_finalize_task_manager();
    if lean_io_result_is_ok(main_res) {
      ret_val = lean_unbox_uint32(lean_io_result_get_value(main_res)) as i32;
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
