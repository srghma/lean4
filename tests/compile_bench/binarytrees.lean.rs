// Lean compiler output
// Module: binarytrees
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_uint32_dec_eq(_: u32, _: u32) -> u8;
    fn lean_uint32_sub(_: u32, _: u32) -> u32;
    fn lean_uint32_add(_: u32, _: u32) -> u32;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_task_get_own(_: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_to_nat(_: u32) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_of_nat(_: *mut lean_object) -> u32;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_pow(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_task_spawn(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static mut l_instInhabitedTree: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_make_x27___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_make_x27___closed__0: *mut lean_object = core::ptr::addr_of!(l_make_x27___closed__0_value) as *mut lean_object;
#[no_mangle] pub static mut l_minN: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_out___closed__0_value: lean_string_object<11> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [32, 111, 102, 32, 100, 101, 112, 116, 104, 32, 0]};
static mut l_out___closed__0: *mut lean_object = core::ptr::addr_of!(l_out___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_out___closed__1_value: lean_string_object<10> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [9, 32, 99, 104, 101, 99, 107, 58, 32, 0]};
static mut l_out___closed__1: *mut lean_object = core::ptr::addr_of!(l_out___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_List_forM___at___00main_spec__0___closed__0_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [9, 32, 116, 114, 101, 101, 115, 0]};
static mut l_List_forM___at___00main_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_forM___at___00main_spec__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<13> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 116, 114, 101, 116, 99, 104, 32, 116, 114, 101, 101, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<16> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [108, 111, 110, 103, 32, 108, 105, 118, 101, 100, 32, 116, 114, 101, 101, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
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
#[no_mangle] pub unsafe extern "C" fn l_depth___lam__0(mut v_d_133_: *mut lean_object, mut v_n_134_: *mut lean_object, mut v_x_135_: *mut lean_object) -> u32{
let mut v___x_136_: u32 = 0; let mut v___x_137_: u32 = 0; let mut v___x_138_: u32 = 0; let mut v___x_139_: u32 = 0; 
v___x_136_ = lean_uint32_of_nat(v_d_133_);
v___x_137_ = lean_uint32_of_nat(v_n_134_);
v___x_138_ = 0;
v___x_139_ = l_sumT(v___x_136_, v___x_137_, v___x_138_);
return v___x_139_;
}
#[no_mangle] pub unsafe extern "C" fn l_depth___lam__0___boxed(mut v_d_140_: *mut lean_object, mut v_n_141_: *mut lean_object, mut v_x_142_: *mut lean_object) -> *mut lean_object{
let mut v_res_143_: u32 = 0; let mut v_r_144_: *mut lean_object = core::ptr::null_mut(); 
v_res_143_ = l_depth___lam__0(v_d_140_, v_n_141_, v_x_142_);
lean_dec(v_n_141_);
lean_dec(v_d_140_);
v_r_144_ = lean_box_uint32(v_res_143_);
return v_r_144_;
}
#[no_mangle] pub unsafe extern "C" fn l_depth(mut v_d_145_: *mut lean_object, mut v_m_146_: *mut lean_object) -> *mut lean_object{
let mut v___x_147_: u8 = 0; 
v___x_147_ = lean_nat_dec_le(v_d_145_, v_m_146_);
if v___x_147_ == 0 {
let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_d_145_);
v___x_148_ = lean_box(0);
return v___x_148_;
} else {
let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v_n_153_: *mut lean_object = core::ptr::null_mut(); let mut v___f_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); 
v___x_149_ = lean_unsigned_to_nat(2);
v___x_150_ = lean_nat_sub(v_m_146_, v_d_145_);
v___x_151_ = lean_unsigned_to_nat(4);
v___x_152_ = lean_nat_add(v___x_150_, v___x_151_);
lean_dec(v___x_150_);
v_n_153_ = lean_nat_pow(v___x_149_, v___x_152_);
lean_dec(v___x_152_);
lean_inc(v_n_153_);
lean_inc_n(v_d_145_, 2);
v___f_154_ = lean_alloc_closure(l_depth___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_154_, 0, v_d_145_);
lean_closure_set(v___f_154_, 1, v_n_153_);
v___x_155_ = lean_unsigned_to_nat(0);
v___x_156_ = lean_task_spawn(v___f_154_, v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_157_, 0, v_d_145_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_158_, 0, v_n_153_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_nat_add(v_d_145_, v___x_149_);
lean_dec(v_d_145_);
v___x_160_ = l_depth(v___x_159_, v_m_146_);
v___x_161_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_161_, 0, v___x_158_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
return v___x_161_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_depth___boxed(mut v_d_162_: *mut lean_object, mut v_m_163_: *mut lean_object) -> *mut lean_object{
let mut v_res_164_: *mut lean_object = core::ptr::null_mut(); 
v_res_164_ = l_depth(v_d_162_, v_m_163_);
lean_dec(v_m_163_);
return v_res_164_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forM___at___00main_spec__0(mut v_as_166_: *mut lean_object) -> *mut lean_object{
let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v_head_170_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_171_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_172_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_173_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_174_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_180_: u32 = 0; let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_as_166_) == 0 {
let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
v___x_168_ = lean_box(0);
v___x_169_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
} else {
let mut v_head_170_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_171_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_172_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_173_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_174_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_180_: u32 = 0; let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); 
v_head_170_ = lean_ctor_get(v_as_166_, 0);
lean_inc(v_head_170_);
v_snd_171_ = lean_ctor_get(v_head_170_, 1);
lean_inc(v_snd_171_);
v_tail_172_ = lean_ctor_get(v_as_166_, 1);
lean_inc(v_tail_172_);
lean_dec_ref_known(v_as_166_, 2);
v_fst_173_ = lean_ctor_get(v_head_170_, 0);
lean_inc(v_fst_173_);
lean_dec(v_head_170_);
v_fst_174_ = lean_ctor_get(v_snd_171_, 0);
lean_inc(v_fst_174_);
v_snd_175_ = lean_ctor_get(v_snd_171_, 1);
lean_inc(v_snd_175_);
lean_dec(v_snd_171_);
v___x_176_ = l_Nat_reprFast(v_fst_173_);
v___x_177_ = l_List_forM___at___00main_spec__0___closed__0;
v___x_178_ = lean_string_append(v___x_176_, v___x_177_);
v___x_179_ = lean_task_get_own(v_snd_175_);
v___x_180_ = lean_unbox_uint32(v___x_179_);
lean_dec(v___x_179_);
v___x_181_ = l_out(v___x_178_, v_fst_174_, v___x_180_);
if lean_obj_tag(v___x_181_) == 0 {
lean_dec_ref_known(v___x_181_, 1);
v_as_166_ = v_tail_172_;
state = 0; continue;
} else {
lean_dec(v_tail_172_);
return v___x_181_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_forM___at___00main_spec__0___boxed(mut v_as_183_: *mut lean_object, mut v___y_184_: *mut lean_object) -> *mut lean_object{
let mut v_res_185_: *mut lean_object = core::ptr::null_mut(); 
v_res_185_ = l_List_forM___at___00main_spec__0(v_as_183_);
return v_res_185_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_188_: u32 = 0; let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); 
v___x_188_ = 1;
v___x_189_ = lean_box_uint32(v___x_188_);
return v___x_189_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__2() -> *mut lean_object{
let mut v___x_190_: u32 = 0; let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); 
v___x_190_ = 0;
v___x_191_ = lean_box_uint32(v___x_190_);
return v___x_191_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_x_192_: *mut lean_object) -> *mut lean_object{
let mut v___x_195_: *mut lean_object = core::ptr::null_mut(); let mut v___x_196_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_197_: *mut lean_object = core::ptr::null_mut(); let mut v_head_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v_n_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v___y_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); let mut v_stretchN_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: u32 = 0; let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v_c_210_: u32 = 0; let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: u32 = 0; let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: u32 = 0; let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_222_: u8 = 0; let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_226_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_227_: u8 = 0; let mut v_unused_228_: *mut lean_object = core::ptr::null_mut(); let mut v_a_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_232_: u8 = 0; let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_235_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_236_: u8 = 0; let mut v_a_237_: *mut lean_object = core::ptr::null_mut(); let mut v___x_239_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_240_: u8 = 0; let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_243_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_244_: u8 = 0; let mut v_a_245_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_248_: u8 = 0; let mut v___x_250_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_252_: u8 = 0; let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_192_) == 1 {
let mut v_tail_197_: *mut lean_object = core::ptr::null_mut(); 
v_tail_197_ = lean_ctor_get(v_x_192_, 1);
if lean_obj_tag(v_tail_197_) == 0 {
let mut v_head_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v_n_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v___y_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254_: u8 = 0; 
v_head_198_ = lean_ctor_get(v_x_192_, 0);
lean_inc(v_head_198_);
lean_dec_ref_known(v_x_192_, 2);
v___x_199_ = lean_unsigned_to_nat(0);
v___x_200_ = lean_string_utf8_byte_size(v_head_198_);
v___x_201_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_201_, 0, v_head_198_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
v_n_202_ = l_String_Slice_toNat_x21(v___x_201_);
lean_dec_ref_known(v___x_201_, 3);
v___x_203_ = lean_unsigned_to_nat(4);
v___x_253_ = lean_unsigned_to_nat(6);
v___x_254_ = lean_nat_dec_le(v___x_253_, v_n_202_);
if v___x_254_ == 0 {
lean_dec(v_n_202_);
v___y_205_ = v___x_253_;
state = 2; continue;
} else {
v___y_205_ = v_n_202_;
state = 2; continue;
}
} else {
lean_dec_ref_known(v_x_192_, 2);
state = 1; continue;
}
} else {
lean_dec(v_x_192_);
state = 1; continue;
}
}
1 => {
v___x_195_ = l_main___boxed__const__1;
v___x_196_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
2 => {
v___x_206_ = lean_unsigned_to_nat(1);
v_stretchN_207_ = lean_nat_add(v___y_205_, v___x_206_);
v___x_208_ = lean_uint32_of_nat(v_stretchN_207_);
v___x_209_ = l_make_x27(v___x_208_, v___x_208_);
v_c_210_ = l_check(v___x_209_);
lean_dec(v___x_209_);
v___x_211_ = l_main___closed__0;
v___x_212_ = l_out(v___x_211_, v_stretchN_207_, v_c_210_);
if lean_obj_tag(v___x_212_) == 0 {
let mut v___x_213_: u32 = 0; let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_212_, 1);
v___x_213_ = lean_uint32_of_nat(v___y_205_);
v___x_214_ = l_make_x27(v___x_213_, v___x_213_);
v___x_215_ = l_depth(v___x_203_, v___y_205_);
v___x_216_ = l_List_forM___at___00main_spec__0(v___x_215_);
if lean_obj_tag(v___x_216_) == 0 {
let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: u32 = 0; let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_216_, 1);
v___x_217_ = l_main___closed__1;
v___x_218_ = l_check(v___x_214_);
lean_dec(v___x_214_);
v___x_219_ = l_out(v___x_217_, v___y_205_, v___x_218_);
if lean_obj_tag(v___x_219_) == 0 {
let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_222_: u8 = 0; let mut v_isSharedCheck_227_: u8 = 0; 
v_isSharedCheck_227_ = (!lean_is_exclusive(v___x_219_)) as u8;
if v_isSharedCheck_227_ == 0 {
let mut v_unused_228_: *mut lean_object = core::ptr::null_mut(); 
v_unused_228_ = lean_ctor_get(v___x_219_, 0);
lean_dec(v_unused_228_);
v___x_221_ = v___x_219_;
v_isShared_222_ = v_isSharedCheck_227_;
state = 3; continue;
} else {
lean_dec(v___x_219_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
state = 3; continue;
}
} else {
let mut v_a_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_232_: u8 = 0; let mut v_isSharedCheck_236_: u8 = 0; 
v_a_229_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_236_ = (!lean_is_exclusive(v___x_219_)) as u8;
if v_isSharedCheck_236_ == 0 {
v___x_231_ = v___x_219_;
v_isShared_232_ = v_isSharedCheck_236_;
state = 5; continue;
} else {
lean_inc(v_a_229_);
lean_dec(v___x_219_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
state = 5; continue;
}
}
} else {
let mut v_a_237_: *mut lean_object = core::ptr::null_mut(); let mut v___x_239_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_240_: u8 = 0; let mut v_isSharedCheck_244_: u8 = 0; 
lean_dec(v___x_214_);
lean_dec(v___y_205_);
v_a_237_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_244_ = (!lean_is_exclusive(v___x_216_)) as u8;
if v_isSharedCheck_244_ == 0 {
v___x_239_ = v___x_216_;
v_isShared_240_ = v_isSharedCheck_244_;
state = 7; continue;
} else {
lean_inc(v_a_237_);
lean_dec(v___x_216_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
state = 7; continue;
}
}
} else {
let mut v_a_245_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_248_: u8 = 0; let mut v_isSharedCheck_252_: u8 = 0; 
lean_dec(v___y_205_);
v_a_245_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_252_ = (!lean_is_exclusive(v___x_212_)) as u8;
if v_isSharedCheck_252_ == 0 {
v___x_247_ = v___x_212_;
v_isShared_248_ = v_isSharedCheck_252_;
state = 9; continue;
} else {
lean_inc(v_a_245_);
lean_dec(v___x_212_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
state = 9; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_x_255_: *mut lean_object, mut v_a_256_: *mut lean_object) -> *mut lean_object{
let mut v_res_257_: *mut lean_object = core::ptr::null_mut(); 
v_res_257_ = _lean_main(v_x_255_);
return v_res_257_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_binarytrees(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
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
  let res = initialize_binarytrees(1 /* builtin */);
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
