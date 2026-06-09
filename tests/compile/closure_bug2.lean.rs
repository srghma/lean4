// Lean compiler output
// Module: closure_bug2
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::String::Slice::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Defs::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
pub static l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0___closed__0_value) as *mut lean_object;
pub static l_List_toString___at___00f_spec__0___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00f_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00f_spec__0___closed__0_value) as *mut lean_object;
pub static l_List_toString___at___00f_spec__0___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00f_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00f_spec__0___closed__1_value) as *mut lean_object;
pub static l_List_toString___at___00f_spec__0___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00f_spec__0___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00f_spec__0___closed__2_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0(mut v_x_2_: *mut lean_object, mut v_x_3_: *mut lean_object) -> *mut lean_object{
let mut v_head_4_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_5_: *mut lean_object = core::ptr::null_mut(); let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_3_) == 0 {
return v_x_2_;
} else {
v_head_4_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_head_4_);
v_tail_5_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_tail_5_);
lean_dec_ref_known(v_x_3_, 2);
v___x_6_ = l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0___closed__0;
v___x_7_ = lean_string_append(v_x_2_, v___x_6_);
v___x_8_ = l_Nat_reprFast(v_head_4_);
v___x_9_ = lean_string_append(v___x_7_, v___x_8_);
lean_dec_ref(v___x_8_);
v_x_2_ = v___x_9_;
v_x_3_ = v_tail_5_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00f_spec__0(mut v_x_14_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_14_) == 0 {
let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_15_ = l_List_toString___at___00f_spec__0___closed__0;
return v___x_15_;
} else {
let mut v_tail_16_: *mut lean_object = core::ptr::null_mut(); 
v_tail_16_ = lean_ctor_get(v_x_14_, 1);
if lean_obj_tag(v_tail_16_) == 0 {
let mut v_head_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); 
v_head_17_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_17_);
lean_dec_ref_known(v_x_14_, 2);
v___x_18_ = l_List_toString___at___00f_spec__0___closed__1;
v___x_19_ = l_Nat_reprFast(v_head_17_);
v___x_20_ = lean_string_append(v___x_18_, v___x_19_);
lean_dec_ref(v___x_19_);
v___x_21_ = l_List_toString___at___00f_spec__0___closed__2;
v___x_22_ = lean_string_append(v___x_20_, v___x_21_);
return v___x_22_;
} else {
let mut v_head_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: u32 = 0; let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_tail_16_);
v_head_23_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_23_);
lean_dec_ref_known(v_x_14_, 2);
v___x_24_ = l_List_toString___at___00f_spec__0___closed__1;
v___x_25_ = l_Nat_reprFast(v_head_23_);
v___x_26_ = lean_string_append(v___x_24_, v___x_25_);
lean_dec_ref(v___x_25_);
v___x_27_ = l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0(v___x_26_, v_tail_16_);
v___x_28_ = 93;
v___x_29_ = lean_string_push(v___x_27_, v___x_28_);
return v___x_29_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_f___lam__0(mut v_00x17_30_: *mut lean_object, mut v_00x16_31_: *mut lean_object, mut v_00x15_32_: *mut lean_object, mut v_00x14_33_: *mut lean_object, mut v_00x13_34_: *mut lean_object, mut v_00x12_35_: *mut lean_object, mut v_00x11_36_: *mut lean_object, mut v_00x10_37_: *mut lean_object, mut v_x9_38_: *mut lean_object, mut v_x8_39_: *mut lean_object, mut v_x7_40_: *mut lean_object, mut v_x6_41_: *mut lean_object, mut v_x5_42_: *mut lean_object, mut v_x4_43_: *mut lean_object, mut v_x3_44_: *mut lean_object, mut v_x2_45_: *mut lean_object, mut v_x1_46_: *mut lean_object, mut v_y_47_: *mut lean_object) -> *mut lean_object{
let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); 
v___x_48_ = lean_box(0);
v___x_49_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_49_, 0, v_00x17_30_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_50_, 0, v_00x16_31_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_51_, 0, v_00x15_32_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_52_, 0, v_00x14_33_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_53_, 0, v_00x13_34_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_54_, 0, v_00x12_35_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_55_, 0, v_00x11_36_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_56_, 0, v_00x10_37_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_57_, 0, v_x9_38_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_58_, 0, v_x8_39_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_59_, 0, v_x7_40_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_60_, 0, v_x6_41_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_61_, 0, v_x5_42_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_62_, 0, v_x4_43_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_63_, 0, v_x3_44_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_64_, 0, v_x2_45_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_65_, 0, v_x1_46_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = l_List_toString___at___00f_spec__0(v___x_65_);
return v___x_66_;
}
#[no_mangle] pub unsafe extern "C" fn l_f___lam__0___boxed(_args: *mut *mut lean_object) -> *mut lean_object{
let mut v_00x17_67_: *mut lean_object = *_args.add(0);
let mut v_00x16_68_: *mut lean_object = *_args.add(1);
let mut v_00x15_69_: *mut lean_object = *_args.add(2);
let mut v_00x14_70_: *mut lean_object = *_args.add(3);
let mut v_00x13_71_: *mut lean_object = *_args.add(4);
let mut v_00x12_72_: *mut lean_object = *_args.add(5);
let mut v_00x11_73_: *mut lean_object = *_args.add(6);
let mut v_00x10_74_: *mut lean_object = *_args.add(7);
let mut v_x9_75_: *mut lean_object = *_args.add(8);
let mut v_x8_76_: *mut lean_object = *_args.add(9);
let mut v_x7_77_: *mut lean_object = *_args.add(10);
let mut v_x6_78_: *mut lean_object = *_args.add(11);
let mut v_x5_79_: *mut lean_object = *_args.add(12);
let mut v_x4_80_: *mut lean_object = *_args.add(13);
let mut v_x3_81_: *mut lean_object = *_args.add(14);
let mut v_x2_82_: *mut lean_object = *_args.add(15);
let mut v_x1_83_: *mut lean_object = *_args.add(16);
let mut v_y_84_: *mut lean_object = *_args.add(17);
let mut v_res_85_: *mut lean_object = core::ptr::null_mut(); 
v_res_85_ = l_f___lam__0(v_00x17_67_, v_00x16_68_, v_00x15_69_, v_00x14_70_, v_00x13_71_, v_00x12_72_, v_00x11_73_, v_00x10_74_, v_x9_75_, v_x8_76_, v_x7_77_, v_x6_78_, v_x5_79_, v_x4_80_, v_x3_81_, v_x2_82_, v_x1_83_, v_y_84_);
lean_dec(v_y_84_);
return v_res_85_;
}
#[no_mangle] pub unsafe extern "C" fn l_f(mut v_x_86_: *mut lean_object) -> *mut lean_object{
let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v_x1_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v_x2_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v_x3_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v_x4_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v_x5_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v_x6_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v_x7_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v_x8_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v_x9_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v_00x10_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v_00x11_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v_00x12_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v_00x13_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); let mut v_00x14_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v_00x15_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); let mut v_00x16_118_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v_00x17_120_: *mut lean_object = core::ptr::null_mut(); let mut v___f_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); 
v___x_87_ = lean_unsigned_to_nat(1);
v_x1_88_ = lean_nat_add(v_x_86_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(2);
v_x2_90_ = lean_nat_add(v_x_86_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(3);
v_x3_92_ = lean_nat_add(v_x_86_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(4);
v_x4_94_ = lean_nat_add(v_x_86_, v___x_93_);
v___x_95_ = lean_unsigned_to_nat(5);
v_x5_96_ = lean_nat_add(v_x_86_, v___x_95_);
v___x_97_ = lean_unsigned_to_nat(6);
v_x6_98_ = lean_nat_add(v_x_86_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(7);
v_x7_100_ = lean_nat_add(v_x_86_, v___x_99_);
v___x_101_ = lean_unsigned_to_nat(8);
v_x8_102_ = lean_nat_add(v_x_86_, v___x_101_);
v___x_103_ = lean_unsigned_to_nat(9);
v_x9_104_ = lean_nat_add(v_x_86_, v___x_103_);
v___x_105_ = lean_unsigned_to_nat(10);
v_00x10_106_ = lean_nat_add(v_x_86_, v___x_105_);
v___x_107_ = lean_unsigned_to_nat(11);
v_00x11_108_ = lean_nat_add(v_x_86_, v___x_107_);
v___x_109_ = lean_unsigned_to_nat(12);
v_00x12_110_ = lean_nat_add(v_x_86_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(13);
v_00x13_112_ = lean_nat_add(v_x_86_, v___x_111_);
v___x_113_ = lean_unsigned_to_nat(14);
v_00x14_114_ = lean_nat_add(v_x_86_, v___x_113_);
v___x_115_ = lean_unsigned_to_nat(15);
v_00x15_116_ = lean_nat_add(v_x_86_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(16);
v_00x16_118_ = lean_nat_add(v_x_86_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(17);
v_00x17_120_ = lean_nat_add(v_x_86_, v___x_119_);
v___f_121_ = lean_alloc_closure(l_f___lam__0___boxed as *mut core::ffi::c_void, 18, 17);
lean_closure_set(v___f_121_, 0, v_00x17_120_);
lean_closure_set(v___f_121_, 1, v_00x16_118_);
lean_closure_set(v___f_121_, 2, v_00x15_116_);
lean_closure_set(v___f_121_, 3, v_00x14_114_);
lean_closure_set(v___f_121_, 4, v_00x13_112_);
lean_closure_set(v___f_121_, 5, v_00x12_110_);
lean_closure_set(v___f_121_, 6, v_00x11_108_);
lean_closure_set(v___f_121_, 7, v_00x10_106_);
lean_closure_set(v___f_121_, 8, v_x9_104_);
lean_closure_set(v___f_121_, 9, v_x8_102_);
lean_closure_set(v___f_121_, 10, v_x7_100_);
lean_closure_set(v___f_121_, 11, v_x6_98_);
lean_closure_set(v___f_121_, 12, v_x5_96_);
lean_closure_set(v___f_121_, 13, v_x4_94_);
lean_closure_set(v___f_121_, 14, v_x3_92_);
lean_closure_set(v___f_121_, 15, v_x2_90_);
lean_closure_set(v___f_121_, 16, v_x1_88_);
v___x_122_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_122_, 0, v_x_86_);
lean_ctor_set(v___x_122_, 1, v___f_121_);
return v___x_122_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_123_: *mut lean_object) -> *mut lean_object{
let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); 
v___x_125_ = lean_get_stdout();
v_putStr_126_ = lean_ctor_get(v___x_125_, 4);
lean_inc_ref(v_putStr_126_);
lean_dec_ref(v___x_125_);
v___x_127_ = lean_apply_2(v_putStr_126_, v_s_123_, lean_box(0));
return v___x_127_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_128_: *mut lean_object, mut v_a_129_: *mut lean_object) -> *mut lean_object{
let mut v_res_130_: *mut lean_object = core::ptr::null_mut(); 
v_res_130_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_128_);
return v_res_130_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_131_: *mut lean_object) -> *mut lean_object{
let mut v___x_133_: u32 = 0; let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); 
v___x_133_ = 10;
v___x_134_ = lean_string_push(v_s_131_, v___x_133_);
v___x_135_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_134_);
return v___x_135_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_136_: *mut lean_object, mut v_a_137_: *mut lean_object) -> *mut lean_object{
let mut v_res_138_: *mut lean_object = core::ptr::null_mut(); 
v_res_138_ = l_IO_println___at___00main_spec__0(v_s_136_);
return v_res_138_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_140_: *mut lean_object) -> *mut lean_object{
let mut v___y_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v_head_153_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_xs_140_) == 0 {
v___x_152_ = l_main___closed__0;
v___y_143_ = v___x_152_;
state = 1; continue;
} else {
v_head_153_ = lean_ctor_get(v_xs_140_, 0);
lean_inc(v_head_153_);
lean_dec_ref_known(v_xs_140_, 2);
v___y_143_ = v_head_153_;
state = 1; continue;
}
}
1 => {
v___x_144_ = lean_unsigned_to_nat(0);
v___x_145_ = lean_string_utf8_byte_size(v___y_143_);
v___x_146_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_146_, 0, v___y_143_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
v___x_147_ = l_String_Slice_toNat_x21(v___x_146_);
lean_dec_ref_known(v___x_146_, 3);
lean_inc(v___x_147_);
v___x_148_ = l_f(v___x_147_);
v_snd_149_ = lean_ctor_get(v___x_148_, 1);
lean_inc(v_snd_149_);
lean_dec_ref(v___x_148_);
v___x_150_ = lean_apply_1(v_snd_149_, v___x_147_);
v___x_151_ = l_IO_println___at___00main_spec__0(v___x_150_);
return v___x_151_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_154_: *mut lean_object, mut v_a_155_: *mut lean_object) -> *mut lean_object{
let mut v_res_156_: *mut lean_object = core::ptr::null_mut(); 
v_res_156_ = _lean_main(v_xs_154_);
return v_res_156_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_closure__bug2(builtin: u8) -> *mut lean_object {
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
  let res = initialize_closure__bug2(1 /* builtin */);
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
