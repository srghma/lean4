// Lean compiler output
// Module: compact_closure_cross
// Imports: public import Init public meta import Init public import Lean.CompactedRegion
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_io_app_path() -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_IO_Process_run(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_compacted_region_read(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_io_remove_file(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Name_mkStr1(_: *mut lean_object) -> *mut lean_object;
    fn lean_compacted_region_save(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: u8) -> *mut lean_object;
}
#[no_mangle] pub static l_main___lam__0___closed__0_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 114, 111, 115, 115, 32, 0]};
static mut l_main___lam__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___lam__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*0 + 8) as u16, m_other: 0, m_tag: 0 }, m_objs: [65793 as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 97, 118, 101, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_array_object<1> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*1) as u16, m_other: 0, m_tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__4_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 111, 97, 100, 0]};
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__5_value: lean_array_object<1> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*1) as u16, m_other: 0, m_tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object] };
static mut l_main___closed__5: *mut lean_object = core::ptr::addr_of!(l_main___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__6_value: lean_string_object<36> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [46, 47, 95, 99, 111, 109, 112, 97, 99, 116, 95, 99, 108, 111, 115, 117, 114, 101, 95, 99, 114, 111, 115, 115, 95, 116, 101, 115, 116, 46, 111, 108, 101, 97, 110, 0]};
static mut l_main___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__7_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__8_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__8: *mut lean_object = core::ptr::addr_of!(l_main___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__9_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 115, 116, 0]};
static mut l_main___closed__9: *mut lean_object = core::ptr::addr_of!(l_main___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__10_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__9_value) as *mut lean_object,13563890123683549843 as *mut lean_object] };
static mut l_main___closed__10: *mut lean_object = core::ptr::addr_of!(l_main___closed__10_value) as *mut lean_object;
#[no_mangle] pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00main_spec__0(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00main_spec__0___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00main_spec__0(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v_n_10_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = l_main___lam__0___closed__0;
v___x_12_ = l_Nat_reprFast(v_n_10_);
v___x_13_ = lean_string_append(v___x_11_, v___x_12_);
lean_dec_ref(v___x_12_);
return v___x_13_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_14_: *mut lean_object) -> *mut lean_object{
let mut v___x_16_: u32 = 0; let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); 
v___x_16_ = 10;
v___x_17_ = lean_string_push(v_s_14_, v___x_16_);
v___x_18_ = l_IO_print___at___00main_spec__0(v___x_17_);
return v___x_18_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_19_: *mut lean_object, mut v_a_20_: *mut lean_object) -> *mut lean_object{
let mut v_res_21_: *mut lean_object = core::ptr::null_mut(); 
v_res_21_ = l_IO_println___at___00main_spec__1(v_s_19_);
return v_res_21_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_43_: u32 = 0; let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
v___x_43_ = 0;
v___x_44_ = lean_box_uint32(v___x_43_);
return v___x_44_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_args_45_: *mut lean_object) -> *mut lean_object{
let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v_a_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: u8 = 0; let mut v___x_55_: u8 = 0; let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v_a_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_65_: u8 = 0; let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_69_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_70_: u8 = 0; let mut v_unused_71_: *mut lean_object = core::ptr::null_mut(); let mut v_a_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_75_: u8 = 0; let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_78_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_79_: u8 = 0; let mut v_a_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_83_: u8 = 0; let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_86_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_87_: u8 = 0; let mut v_a_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_91_: u8 = 0; let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_94_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_95_: u8 = 0; let mut v_a_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_99_: u8 = 0; let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_102_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_103_: u8 = 0; let mut v_head_104_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_105_: *mut lean_object = core::ptr::null_mut(); let mut v_tmpFile_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: u8 = 0; let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: u8 = 0; let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v_a_113_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_124_: u8 = 0; let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_128_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_129_: u8 = 0; let mut v_unused_130_: *mut lean_object = core::ptr::null_mut(); let mut v_a_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_134_: u8 = 0; let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_137_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_138_: u8 = 0; let mut v_a_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_142_: u8 = 0; let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_145_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_146_: u8 = 0; let mut v_a_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_150_: u8 = 0; let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_153_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_154_: u8 = 0; let mut v_a_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_158_: u8 = 0; let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_161_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_162_: u8 = 0; let mut v_f_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_170_: u8 = 0; let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_174_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_175_: u8 = 0; let mut v_unused_176_: *mut lean_object = core::ptr::null_mut(); let mut v_a_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_180_: u8 = 0; let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_183_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_184_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_args_45_) == 1 {
let mut v_head_104_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_105_: *mut lean_object = core::ptr::null_mut(); let mut v_tmpFile_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: u8 = 0; 
v_head_104_ = lean_ctor_get(v_args_45_, 0);
lean_inc(v_head_104_);
v_tail_105_ = lean_ctor_get(v_args_45_, 1);
lean_inc(v_tail_105_);
lean_dec_ref_known(v_args_45_, 2);
v_tmpFile_106_ = l_main___closed__6;
v___x_107_ = l_main___closed__1;
v___x_108_ = lean_string_dec_eq(v_head_104_, v___x_107_);
if v___x_108_ == 0 {
let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: u8 = 0; 
v___x_109_ = l_main___closed__4;
v___x_110_ = lean_string_dec_eq(v_head_104_, v___x_109_);
lean_dec(v_head_104_);
if v___x_110_ == 0 {
lean_dec(v_tail_105_);
state = 1; continue;
} else {
if lean_obj_tag(v_tail_105_) == 0 {
let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); 
v___x_111_ = l_main___closed__7;
v___x_112_ = lean_compacted_region_read(v_tmpFile_106_, v___x_111_);
if lean_obj_tag(v___x_112_) == 0 {
let mut v_a_113_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_112_, 1);
v_fst_114_ = lean_ctor_get(v_a_113_, 0);
lean_inc_n(v_fst_114_, 2);
lean_dec(v_a_113_);
v___x_115_ = lean_unsigned_to_nat(7);
v___x_116_ = lean_apply_1(v_fst_114_, v___x_115_);
v___x_117_ = l_IO_println___at___00main_spec__1(v___x_116_);
if lean_obj_tag(v___x_117_) == 0 {
let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_117_, 1);
v___x_118_ = lean_unsigned_to_nat(99);
v___x_119_ = lean_apply_1(v_fst_114_, v___x_118_);
v___x_120_ = l_IO_println___at___00main_spec__1(v___x_119_);
if lean_obj_tag(v___x_120_) == 0 {
let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_120_, 1);
v___x_121_ = lean_io_remove_file(v_tmpFile_106_);
if lean_obj_tag(v___x_121_) == 0 {
let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_124_: u8 = 0; let mut v_isSharedCheck_129_: u8 = 0; 
v_isSharedCheck_129_ = (!lean_is_exclusive(v___x_121_)) as u8;
if v_isSharedCheck_129_ == 0 {
let mut v_unused_130_: *mut lean_object = core::ptr::null_mut(); 
v_unused_130_ = lean_ctor_get(v___x_121_, 0);
lean_dec(v_unused_130_);
v___x_123_ = v___x_121_;
v_isShared_124_ = v_isSharedCheck_129_;
state = 12; continue;
} else {
lean_dec(v___x_121_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
state = 12; continue;
}
} else {
let mut v_a_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_134_: u8 = 0; let mut v_isSharedCheck_138_: u8 = 0; 
v_a_131_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_138_ = (!lean_is_exclusive(v___x_121_)) as u8;
if v_isSharedCheck_138_ == 0 {
v___x_133_ = v___x_121_;
v_isShared_134_ = v_isSharedCheck_138_;
state = 14; continue;
} else {
lean_inc(v_a_131_);
lean_dec(v___x_121_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
state = 14; continue;
}
}
} else {
let mut v_a_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_142_: u8 = 0; let mut v_isSharedCheck_146_: u8 = 0; 
v_a_139_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_146_ = (!lean_is_exclusive(v___x_120_)) as u8;
if v_isSharedCheck_146_ == 0 {
v___x_141_ = v___x_120_;
v_isShared_142_ = v_isSharedCheck_146_;
state = 16; continue;
} else {
lean_inc(v_a_139_);
lean_dec(v___x_120_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
state = 16; continue;
}
}
} else {
let mut v_a_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_150_: u8 = 0; let mut v_isSharedCheck_154_: u8 = 0; 
lean_dec(v_fst_114_);
v_a_147_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_154_ = (!lean_is_exclusive(v___x_117_)) as u8;
if v_isSharedCheck_154_ == 0 {
v___x_149_ = v___x_117_;
v_isShared_150_ = v_isSharedCheck_154_;
state = 18; continue;
} else {
lean_inc(v_a_147_);
lean_dec(v___x_117_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
state = 18; continue;
}
}
} else {
let mut v_a_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_158_: u8 = 0; let mut v_isSharedCheck_162_: u8 = 0; 
v_a_155_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_162_ = (!lean_is_exclusive(v___x_112_)) as u8;
if v_isSharedCheck_162_ == 0 {
v___x_157_ = v___x_112_;
v_isShared_158_ = v_isSharedCheck_162_;
state = 20; continue;
} else {
lean_inc(v_a_155_);
lean_dec(v___x_112_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
state = 20; continue;
}
}
} else {
lean_dec(v_tail_105_);
state = 1; continue;
}
}
} else {
lean_dec(v_head_104_);
if lean_obj_tag(v_tail_105_) == 0 {
let mut v_f_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); 
v_f_163_ = l_main___closed__8;
v___x_164_ = l_main___closed__10;
v___x_165_ = l_main___closed__7;
v___x_166_ = lean_box(0);
v___x_167_ = lean_compacted_region_save(v_tmpFile_106_, v___x_164_, v_f_163_, v___x_165_, v___x_166_, v___x_108_);
if lean_obj_tag(v___x_167_) == 0 {
let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_170_: u8 = 0; let mut v_isSharedCheck_175_: u8 = 0; 
v_isSharedCheck_175_ = (!lean_is_exclusive(v___x_167_)) as u8;
if v_isSharedCheck_175_ == 0 {
let mut v_unused_176_: *mut lean_object = core::ptr::null_mut(); 
v_unused_176_ = lean_ctor_get(v___x_167_, 0);
lean_dec(v_unused_176_);
v___x_169_ = v___x_167_;
v_isShared_170_ = v_isSharedCheck_175_;
state = 22; continue;
} else {
lean_dec(v___x_167_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
state = 22; continue;
}
} else {
let mut v_a_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_180_: u8 = 0; let mut v_isSharedCheck_184_: u8 = 0; 
v_a_177_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_184_ = (!lean_is_exclusive(v___x_167_)) as u8;
if v_isSharedCheck_184_ == 0 {
v___x_179_ = v___x_167_;
v_isShared_180_ = v_isSharedCheck_184_;
state = 24; continue;
} else {
lean_inc(v_a_177_);
lean_dec(v___x_167_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
state = 24; continue;
}
}
} else {
lean_dec(v_tail_105_);
state = 1; continue;
}
}
} else {
lean_dec(v_args_45_);
state = 1; continue;
}
}
1 => {
v___x_48_ = lean_io_app_path();
if lean_obj_tag(v___x_48_) == 0 {
let mut v_a_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: u8 = 0; let mut v___x_55_: u8 = 0; let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc_n(v_a_49_, 2);
lean_dec_ref_known(v___x_48_, 1);
v___x_50_ = l_main___closed__0;
v___x_51_ = l_main___closed__2;
v___x_52_ = lean_box(0);
v___x_53_ = l_main___closed__3;
v___x_54_ = 1;
v___x_55_ = 0;
v___x_56_ = lean_alloc_ctor(0, 5, (2) as u32);
lean_ctor_set(v___x_56_, 0, v___x_50_);
lean_ctor_set(v___x_56_, 1, v_a_49_);
lean_ctor_set(v___x_56_, 2, v___x_51_);
lean_ctor_set(v___x_56_, 3, v___x_52_);
lean_ctor_set(v___x_56_, 4, v___x_53_);
lean_ctor_set_uint8(v___x_56_, (core::mem::size_of::<*mut lean_object>()*5) as u32, v___x_54_);
lean_ctor_set_uint8(v___x_56_, (core::mem::size_of::<*mut lean_object>()*5 + 1) as u32, v___x_55_);
v___x_57_ = l_IO_Process_run(v___x_56_, v___x_52_);
if lean_obj_tag(v___x_57_) == 0 {
let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_57_, 1);
v___x_58_ = l_main___closed__5;
v___x_59_ = lean_alloc_ctor(0, 5, (2) as u32);
lean_ctor_set(v___x_59_, 0, v___x_50_);
lean_ctor_set(v___x_59_, 1, v_a_49_);
lean_ctor_set(v___x_59_, 2, v___x_58_);
lean_ctor_set(v___x_59_, 3, v___x_52_);
lean_ctor_set(v___x_59_, 4, v___x_53_);
lean_ctor_set_uint8(v___x_59_, (core::mem::size_of::<*mut lean_object>()*5) as u32, v___x_54_);
lean_ctor_set_uint8(v___x_59_, (core::mem::size_of::<*mut lean_object>()*5 + 1) as u32, v___x_55_);
v___x_60_ = l_IO_Process_run(v___x_59_, v___x_52_);
if lean_obj_tag(v___x_60_) == 0 {
let mut v_a_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_60_, 1);
v___x_62_ = l_IO_print___at___00main_spec__0(v_a_61_);
if lean_obj_tag(v___x_62_) == 0 {
let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_65_: u8 = 0; let mut v_isSharedCheck_70_: u8 = 0; 
v_isSharedCheck_70_ = (!lean_is_exclusive(v___x_62_)) as u8;
if v_isSharedCheck_70_ == 0 {
let mut v_unused_71_: *mut lean_object = core::ptr::null_mut(); 
v_unused_71_ = lean_ctor_get(v___x_62_, 0);
lean_dec(v_unused_71_);
v___x_64_ = v___x_62_;
v_isShared_65_ = v_isSharedCheck_70_;
state = 2; continue;
} else {
lean_dec(v___x_62_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_70_;
state = 2; continue;
}
} else {
let mut v_a_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_75_: u8 = 0; let mut v_isSharedCheck_79_: u8 = 0; 
v_a_72_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_79_ = (!lean_is_exclusive(v___x_62_)) as u8;
if v_isSharedCheck_79_ == 0 {
v___x_74_ = v___x_62_;
v_isShared_75_ = v_isSharedCheck_79_;
state = 4; continue;
} else {
lean_inc(v_a_72_);
lean_dec(v___x_62_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
state = 4; continue;
}
}
} else {
let mut v_a_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_83_: u8 = 0; let mut v_isSharedCheck_87_: u8 = 0; 
v_a_80_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_87_ = (!lean_is_exclusive(v___x_60_)) as u8;
if v_isSharedCheck_87_ == 0 {
v___x_82_ = v___x_60_;
v_isShared_83_ = v_isSharedCheck_87_;
state = 6; continue;
} else {
lean_inc(v_a_80_);
lean_dec(v___x_60_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
state = 6; continue;
}
}
} else {
let mut v_a_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_91_: u8 = 0; let mut v_isSharedCheck_95_: u8 = 0; 
lean_dec(v_a_49_);
v_a_88_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_95_ = (!lean_is_exclusive(v___x_57_)) as u8;
if v_isSharedCheck_95_ == 0 {
v___x_90_ = v___x_57_;
v_isShared_91_ = v_isSharedCheck_95_;
state = 8; continue;
} else {
lean_inc(v_a_88_);
lean_dec(v___x_57_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
state = 8; continue;
}
}
} else {
let mut v_a_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_99_: u8 = 0; let mut v_isSharedCheck_103_: u8 = 0; 
v_a_96_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_103_ = (!lean_is_exclusive(v___x_48_)) as u8;
if v_isSharedCheck_103_ == 0 {
v___x_98_ = v___x_48_;
v_isShared_99_ = v_isSharedCheck_103_;
state = 10; continue;
} else {
lean_inc(v_a_96_);
lean_dec(v___x_48_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
state = 10; continue;
}
}
}
12 => {
v___x_125_ = l_main___boxed__const__1;
if v_isShared_124_ == 0 {
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
state = 13; continue;
} else {
let mut v_reuseFailAlloc_128_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
state = 13; continue;
}
}
14 => {
if v_isShared_134_ == 0 {
v___x_136_ = v___x_133_;
state = 15; continue;
} else {
let mut v_reuseFailAlloc_137_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
state = 15; continue;
}
}
16 => {
if v_isShared_142_ == 0 {
v___x_144_ = v___x_141_;
state = 17; continue;
} else {
let mut v_reuseFailAlloc_145_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
state = 17; continue;
}
}
18 => {
if v_isShared_150_ == 0 {
v___x_152_ = v___x_149_;
state = 19; continue;
} else {
let mut v_reuseFailAlloc_153_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
state = 19; continue;
}
}
20 => {
if v_isShared_158_ == 0 {
v___x_160_ = v___x_157_;
state = 21; continue;
} else {
let mut v_reuseFailAlloc_161_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
state = 21; continue;
}
}
22 => {
v___x_171_ = l_main___boxed__const__1;
if v_isShared_170_ == 0 {
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_173_ = v___x_169_;
state = 23; continue;
} else {
let mut v_reuseFailAlloc_174_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
state = 23; continue;
}
}
24 => {
if v_isShared_180_ == 0 {
v___x_182_ = v___x_179_;
state = 25; continue;
} else {
let mut v_reuseFailAlloc_183_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
state = 25; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_args_185_: *mut lean_object, mut v_a_186_: *mut lean_object) -> *mut lean_object{
let mut v_res_187_: *mut lean_object = core::ptr::null_mut(); 
v_res_187_ = _lean_main(v_args_185_);
return v_res_187_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_CompactedRegion(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_compact__closure__cross(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_CompactedRegion(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
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
  let res = initialize_compact__closure__cross(1 /* builtin */);
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
