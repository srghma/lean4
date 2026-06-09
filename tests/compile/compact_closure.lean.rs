// Lean compiler output
// Module: compact_closure
// Imports: Init Init Lean.CompactedRegion
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_lean::Lean::CompactedRegion::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Array::Basic::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Defs::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_compacted_region_save(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: u8) -> *mut lean_object;
    fn lean_compacted_region_read(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_io_remove_file(_: *mut lean_object) -> *mut lean_object;
}
pub static l_main___lam__0___closed__0_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [104, 101, 108, 108, 111, 32, 0]};
static mut l_main___lam__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___lam__0___closed__0_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
pub static l_main___closed__1_value: lean_string_object<30> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [46, 47, 95, 99, 111, 109, 112, 97, 99, 116, 95, 99, 108, 111, 115, 117, 114, 101, 95, 116, 101, 115, 116, 46, 111, 108, 101, 97, 110, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
pub static l_main___closed__2_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 115, 116, 0]};
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
pub static l_main___closed__3_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object,13563890123683549843 as *mut lean_object] };
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
pub static l_main___closed__4_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
pub static l_main___closed__5_value: lean_array_object<3> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*3) as u16, m_other: 0, m_tag: 246 }, m_size: 3, m_capacity: 3, m_data: [((( 10 as usize) << 1) | 1) as *mut lean_object,((( 20 as usize) << 1) | 1) as *mut lean_object,((( 30 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__5: *mut lean_object = core::ptr::addr_of!(l_main___closed__5_value) as *mut lean_object;
pub static l_main___closed__6_value: lean_closure_object<2> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*2) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_main___closed__5_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object;
pub static l_main___closed__7_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 101, 115, 116, 50, 0]};
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
pub static l_main___closed__8_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object,2806259761969496257 as *mut lean_object] };
static mut l_main___closed__8: *mut lean_object = core::ptr::addr_of!(l_main___closed__8_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v_n_2_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = l_main___lam__0___closed__0;
v___x_4_ = l_Nat_reprFast(v_n_2_);
v___x_5_ = lean_string_append(v___x_3_, v___x_4_);
lean_dec_ref(v___x_4_);
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__1(mut v_as_6_: *mut lean_object, mut v_i_7_: usize, mut v_stop_8_: usize, mut v_b_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_10_: u8 = 0; let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: usize = 0; let mut v___x_14_: usize = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_10_ = lean_usize_dec_eq(v_i_7_, v_stop_8_);
if v___x_10_ == 0 {
v___x_11_ = lean_array_uget_borrowed(v_as_6_, v_i_7_);
v___x_12_ = lean_nat_add(v_b_9_, v___x_11_);
lean_dec(v_b_9_);
v___x_13_ = 1usize;
v___x_14_ = lean_usize_add(v_i_7_, v___x_13_);
v_i_7_ = v___x_14_;
v_b_9_ = v___x_12_;
state = 0; continue;
} else {
return v_b_9_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__1___boxed(mut v_as_16_: *mut lean_object, mut v_i_17_: *mut lean_object, mut v_stop_18_: *mut lean_object, mut v_b_19_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_20_: usize = 0; let mut v_stop_boxed_21_: usize = 0; let mut v_res_22_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_20_ = lean_unbox_usize(v_i_17_);
lean_dec(v_i_17_);
v_stop_boxed_21_ = lean_unbox_usize(v_stop_18_);
lean_dec(v_stop_18_);
v_res_22_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__1(v_as_16_, v_i_boxed_20_, v_stop_boxed_21_, v_b_19_);
lean_dec_ref(v_as_16_);
return v_res_22_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__1(mut v___x_23_: *mut lean_object, mut v___x_24_: *mut lean_object, mut v_i_25_: *mut lean_object) -> *mut lean_object{
let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: u8 = 0; 
v___x_26_ = lean_array_get_size(v___x_23_);
v___x_27_ = lean_nat_dec_lt(v___x_24_, v___x_26_);
if v___x_27_ == 0 {
return v_i_25_;
} else {
let mut v___x_28_: u8 = 0; 
v___x_28_ = lean_nat_dec_le(v___x_26_, v___x_26_);
if v___x_28_ == 0 {
if v___x_27_ == 0 {
return v_i_25_;
} else {
let mut v___x_29_: usize = 0; let mut v___x_30_: usize = 0; let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); 
v___x_29_ = 0usize;
v___x_30_ = lean_usize_of_nat(v___x_26_);
v___x_31_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__1(v___x_23_, v___x_29_, v___x_30_, v_i_25_);
return v___x_31_;
}
} else {
let mut v___x_32_: usize = 0; let mut v___x_33_: usize = 0; let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
v___x_32_ = 0usize;
v___x_33_ = lean_usize_of_nat(v___x_26_);
v___x_34_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__1(v___x_23_, v___x_32_, v___x_33_, v_i_25_);
return v___x_34_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__1___boxed(mut v___x_35_: *mut lean_object, mut v___x_36_: *mut lean_object, mut v_i_37_: *mut lean_object) -> *mut lean_object{
let mut v_res_38_: *mut lean_object = core::ptr::null_mut(); 
v_res_38_ = l_main___lam__1(v___x_35_, v___x_36_, v_i_37_);
lean_dec(v___x_36_);
lean_dec_ref(v___x_35_);
return v_res_38_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_39_: *mut lean_object) -> *mut lean_object{
let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); 
v___x_41_ = lean_get_stdout();
v_putStr_42_ = lean_ctor_get(v___x_41_, 4);
lean_inc_ref(v_putStr_42_);
lean_dec_ref(v___x_41_);
v___x_43_ = lean_apply_2(v_putStr_42_, v_s_39_, lean_box(0));
return v___x_43_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_44_: *mut lean_object, mut v_a_45_: *mut lean_object) -> *mut lean_object{
let mut v_res_46_: *mut lean_object = core::ptr::null_mut(); 
v_res_46_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_44_);
return v_res_46_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_47_: *mut lean_object) -> *mut lean_object{
let mut v___x_49_: u32 = 0; let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
v___x_49_ = 10;
v___x_50_ = lean_string_push(v_s_47_, v___x_49_);
v___x_51_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_50_);
return v___x_51_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_52_: *mut lean_object, mut v_a_53_: *mut lean_object) -> *mut lean_object{
let mut v_res_54_: *mut lean_object = core::ptr::null_mut(); 
v_res_54_ = l_IO_println___at___00main_spec__0(v_s_52_);
return v_res_54_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v_f_77_: *mut lean_object = core::ptr::null_mut(); let mut v_tmpFile_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: u8 = 0; let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v_a_86_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___f_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v_a_97_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v_a_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_111_: u8 = 0; let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_114_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_115_: u8 = 0; let mut v_a_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_119_: u8 = 0; let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_122_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_123_: u8 = 0; let mut v_a_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_127_: u8 = 0; let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_130_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_131_: u8 = 0; let mut v_a_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_135_: u8 = 0; let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_138_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_139_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_f_77_ = l_main___closed__0;
v_tmpFile_78_ = l_main___closed__1;
v___x_79_ = l_main___closed__3;
v___x_80_ = lean_unsigned_to_nat(0);
v___x_81_ = l_main___closed__4;
v___x_82_ = lean_box(0);
v___x_83_ = 1;
v___x_84_ = lean_compacted_region_save(v_tmpFile_78_, v___x_79_, v_f_77_, v___x_81_, v___x_82_, v___x_83_);
if lean_obj_tag(v___x_84_) == 0 {
lean_dec_ref_known(v___x_84_, 1);
v___x_85_ = lean_compacted_region_read(v_tmpFile_78_, v___x_81_);
if lean_obj_tag(v___x_85_) == 0 {
v_a_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_a_86_);
lean_dec_ref_known(v___x_85_, 1);
v_fst_87_ = lean_ctor_get(v_a_86_, 0);
lean_inc_n(v_fst_87_, 2);
lean_dec(v_a_86_);
v___x_88_ = lean_unsigned_to_nat(42);
v___x_89_ = lean_apply_1(v_fst_87_, v___x_88_);
v___x_90_ = l_IO_println___at___00main_spec__0(v___x_89_);
if lean_obj_tag(v___x_90_) == 0 {
lean_dec_ref_known(v___x_90_, 1);
v___x_91_ = lean_apply_1(v_fst_87_, v___x_80_);
v___x_92_ = l_IO_println___at___00main_spec__0(v___x_91_);
if lean_obj_tag(v___x_92_) == 0 {
lean_dec_ref_known(v___x_92_, 1);
v___f_93_ = l_main___closed__6;
v___x_94_ = l_main___closed__8;
v___x_95_ = lean_compacted_region_save(v_tmpFile_78_, v___x_94_, v___f_93_, v___x_81_, v___x_82_, v___x_83_);
if lean_obj_tag(v___x_95_) == 0 {
lean_dec_ref_known(v___x_95_, 1);
v___x_96_ = lean_compacted_region_read(v_tmpFile_78_, v___x_81_);
if lean_obj_tag(v___x_96_) == 0 {
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_96_, 1);
v_fst_98_ = lean_ctor_get(v_a_97_, 0);
lean_inc_n(v_fst_98_, 2);
lean_dec(v_a_97_);
v___x_99_ = lean_unsigned_to_nat(1);
v___x_100_ = lean_apply_1(v_fst_98_, v___x_99_);
v___x_101_ = l_Nat_reprFast(v___x_100_);
v___x_102_ = l_IO_println___at___00main_spec__0(v___x_101_);
if lean_obj_tag(v___x_102_) == 0 {
lean_dec_ref_known(v___x_102_, 1);
v___x_103_ = lean_unsigned_to_nat(100);
v___x_104_ = lean_apply_1(v_fst_98_, v___x_103_);
v___x_105_ = l_Nat_reprFast(v___x_104_);
v___x_106_ = l_IO_println___at___00main_spec__0(v___x_105_);
if lean_obj_tag(v___x_106_) == 0 {
lean_dec_ref_known(v___x_106_, 1);
v___x_107_ = lean_io_remove_file(v_tmpFile_78_);
return v___x_107_;
} else {
return v___x_106_;
}
} else {
lean_dec(v_fst_98_);
return v___x_102_;
}
} else {
v_a_108_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_115_ = (!lean_is_exclusive(v___x_96_)) as u8;
if v_isSharedCheck_115_ == 0 {
v___x_110_ = v___x_96_;
v_isShared_111_ = v_isSharedCheck_115_;
state = 1; continue;
} else {
lean_inc(v_a_108_);
lean_dec(v___x_96_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
state = 1; continue;
}
}
} else {
v_a_116_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_123_ = (!lean_is_exclusive(v___x_95_)) as u8;
if v_isSharedCheck_123_ == 0 {
v___x_118_ = v___x_95_;
v_isShared_119_ = v_isSharedCheck_123_;
state = 3; continue;
} else {
lean_inc(v_a_116_);
lean_dec(v___x_95_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
state = 3; continue;
}
}
} else {
return v___x_92_;
}
} else {
lean_dec(v_fst_87_);
return v___x_90_;
}
} else {
v_a_124_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_131_ = (!lean_is_exclusive(v___x_85_)) as u8;
if v_isSharedCheck_131_ == 0 {
v___x_126_ = v___x_85_;
v_isShared_127_ = v_isSharedCheck_131_;
state = 5; continue;
} else {
lean_inc(v_a_124_);
lean_dec(v___x_85_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
state = 5; continue;
}
}
} else {
v_a_132_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_139_ = (!lean_is_exclusive(v___x_84_)) as u8;
if v_isSharedCheck_139_ == 0 {
v___x_134_ = v___x_84_;
v_isShared_135_ = v_isSharedCheck_139_;
state = 7; continue;
} else {
lean_inc(v_a_132_);
lean_dec(v___x_84_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
state = 7; continue;
}
}
}
1 => {
if v_isShared_111_ == 0 {
v___x_113_ = v___x_110_;
state = 2; continue;
} else {
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
state = 2; continue;
}
}
2 => {
return v___x_113_;
}
3 => {
if v_isShared_119_ == 0 {
v___x_121_ = v___x_118_;
state = 4; continue;
} else {
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
state = 4; continue;
}
}
4 => {
return v___x_121_;
}
5 => {
if v_isShared_127_ == 0 {
v___x_129_ = v___x_126_;
state = 6; continue;
} else {
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
state = 6; continue;
}
}
6 => {
return v___x_129_;
}
7 => {
if v_isShared_135_ == 0 {
v___x_137_ = v___x_134_;
state = 8; continue;
} else {
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
state = 8; continue;
}
}
8 => {
return v___x_137_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_140_: *mut lean_object) -> *mut lean_object{
let mut v_res_141_: *mut lean_object = core::ptr::null_mut(); 
v_res_141_ = _lean_main();
return v_res_141_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_compact__closure(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_CompactedRegion(builtin);
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
  lean_initialize();
  let res = initialize_compact__closure(1 /* builtin */);
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
