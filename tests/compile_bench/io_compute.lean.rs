// Lean compiler output
// Module: io_compute
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_array_fget_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_fswap(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_dec_lt(_: u64, _: u64) -> u8;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_shiftr(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_shift_right(_: u64, _: u64) -> u64;
    fn lean_uint64_xor(_: u64, _: u64) -> u64;
    fn lean_uint64_shift_left(_: u64, _: u64) -> u64;
    fn lean_uint64_mul(_: u64, _: u64) -> u64;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    static mut l_instInhabitedUInt64: u64;
    fn lean_array_get_borrowed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_land(_: u64, _: u64) -> u64;
    fn lean_uint64_to_uint8(_: u64) -> u8;
    fn lean_byte_array_push(_: *mut lean_object, _: u8) -> *mut lean_object;
    fn lean_nat_mul(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_byte_array_get(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_uint8_to_uint64(_: u8) -> u64;
    fn lean_uint64_add(_: u64, _: u64) -> u64;
    fn lean_uint64_of_nat(_: *mut lean_object) -> u64;
    fn lean_uint64_mod(_: u64, _: u64) -> u64;
    fn lean_uint64_to_nat(_: u64) -> *mut lean_object;
    fn lean_array_swap(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn l_IO_FS_readBinFile(_: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_io_mono_ms_now() -> *mut lean_object;
    fn lean_float_of_nat(_: *mut lean_object) -> f64;
    fn l_Float_ofScientific(_: *mut lean_object, _: u8, _: *mut lean_object) -> f64;
    fn lean_float_div(_: f64, _: f64) -> f64;
    fn lean_float_to_string(_: f64) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_io_create_tempfile() -> *mut lean_object;
    fn lean_mk_empty_byte_array(_: *mut lean_object) -> *mut lean_object;
    fn l_IO_FS_writeBinFile(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static mut l_N: *mut lean_object = core::ptr::null_mut();
static mut l_timeS___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_timeS___redArg___closed__0: f64 = 0.0;
#[no_mangle] pub static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__0_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 6250000 as usize) << 1) | 1) as *mut lean_object,((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1___boxed__const__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*0 + 8) as u16, m_other: 0, m_tag: 0 }, m_objs: [42 as *mut lean_object] };
#[no_mangle] pub static mut l_main___closed__1___boxed__const__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1___boxed__const__1_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__3_value: lean_string_object<28> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [109, 101, 97, 115, 117, 114, 101, 109, 101, 110, 116, 58, 32, 103, 101, 110, 101, 114, 97, 116, 101, 95, 115, 111, 114, 116, 32, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__4_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 115, 0]};
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__6_value: lean_string_object<20> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [109, 101, 97, 115, 117, 114, 101, 109, 101, 110, 116, 58, 32, 119, 114, 105, 116, 101, 32, 0]};
static mut l_main___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__7_value: lean_string_object<19> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [109, 101, 97, 115, 117, 114, 101, 109, 101, 110, 116, 58, 32, 114, 101, 97, 100, 32, 0]};
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__8_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 6249999 as usize) << 1) | 1) as *mut lean_object,((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__8: *mut lean_object = core::ptr::addr_of!(l_main___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__9_value: lean_string_object<22> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [109, 101, 97, 115, 117, 114, 101, 109, 101, 110, 116, 58, 32, 115, 104, 117, 102, 102, 108, 101, 32, 0]};
static mut l_main___closed__9: *mut lean_object = core::ptr::addr_of!(l_main___closed__9_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn _init_l_N() -> *mut lean_object{
let mut v___x_1_: *mut lean_object = core::ptr::null_mut(); 
v___x_1_ = lean_unsigned_to_nat(6250000);
return v___x_1_;
}
#[no_mangle] pub unsafe extern "C" fn l_xorshift64(mut v_state_2_: u64) -> *mut lean_object{
let mut v___x_3_: u64 = 0; let mut v___x_4_: u64 = 0; let mut v_x_5_: u64 = 0; let mut v___x_6_: u64 = 0; let mut v___x_7_: u64 = 0; let mut v_x_8_: u64 = 0; let mut v___x_9_: u64 = 0; let mut v___x_10_: u64 = 0; let mut v_x_11_: u64 = 0; let mut v___x_12_: u64 = 0; let mut v___x_13_: u64 = 0; let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = 12u64;
v___x_4_ = lean_uint64_shift_right(v_state_2_, v___x_3_);
v_x_5_ = lean_uint64_xor(v_state_2_, v___x_4_);
v___x_6_ = 25u64;
v___x_7_ = lean_uint64_shift_left(v_x_5_, v___x_6_);
v_x_8_ = lean_uint64_xor(v_x_5_, v___x_7_);
v___x_9_ = 27u64;
v___x_10_ = lean_uint64_shift_right(v_x_8_, v___x_9_);
v_x_11_ = lean_uint64_xor(v_x_8_, v___x_10_);
v___x_12_ = 2685821657736338717u64;
v___x_13_ = lean_uint64_mul(v_x_11_, v___x_12_);
v___x_14_ = lean_box_uint64(v_x_11_);
v___x_15_ = lean_box_uint64(v___x_13_);
v___x_16_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_16_, 0, v___x_14_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
return v___x_16_;
}
#[no_mangle] pub unsafe extern "C" fn l_xorshift64___boxed(mut v_state_17_: *mut lean_object) -> *mut lean_object{
let mut v_state_boxed_18_: u64 = 0; let mut v_res_19_: *mut lean_object = core::ptr::null_mut(); 
v_state_boxed_18_ = lean_unbox_uint64(v_state_17_);
lean_dec_ref(v_state_17_);
v_res_19_ = l_xorshift64(v_state_boxed_18_);
return v_res_19_;
}
#[no_mangle] pub unsafe extern "C" fn l_pushLE(mut v_ba_20_: *mut lean_object, mut v_v_21_: u64) -> *mut lean_object{
let mut v___x_22_: u64 = 0; let mut v___x_23_: u64 = 0; let mut v___x_24_: u8 = 0; let mut v_ba_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: u64 = 0; let mut v___x_27_: u64 = 0; let mut v___x_28_: u64 = 0; let mut v___x_29_: u8 = 0; let mut v_ba_30_: *mut lean_object = core::ptr::null_mut(); let mut v___x_31_: u64 = 0; let mut v___x_32_: u64 = 0; let mut v___x_33_: u64 = 0; let mut v___x_34_: u8 = 0; let mut v_ba_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: u64 = 0; let mut v___x_37_: u64 = 0; let mut v___x_38_: u64 = 0; let mut v___x_39_: u8 = 0; let mut v_ba_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: u64 = 0; let mut v___x_42_: u64 = 0; let mut v___x_43_: u64 = 0; let mut v___x_44_: u8 = 0; let mut v_ba_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: u64 = 0; let mut v___x_47_: u64 = 0; let mut v___x_48_: u64 = 0; let mut v___x_49_: u8 = 0; let mut v_ba_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: u64 = 0; let mut v___x_52_: u64 = 0; let mut v___x_53_: u64 = 0; let mut v___x_54_: u8 = 0; let mut v_ba_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: u64 = 0; let mut v___x_57_: u64 = 0; let mut v___x_58_: u64 = 0; let mut v___x_59_: u8 = 0; let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); 
v___x_22_ = 255u64;
v___x_23_ = lean_uint64_land(v_v_21_, v___x_22_);
v___x_24_ = lean_uint64_to_uint8(v___x_23_);
v_ba_25_ = lean_byte_array_push(v_ba_20_, v___x_24_);
v___x_26_ = 8u64;
v___x_27_ = lean_uint64_shift_right(v_v_21_, v___x_26_);
v___x_28_ = lean_uint64_land(v___x_27_, v___x_22_);
v___x_29_ = lean_uint64_to_uint8(v___x_28_);
v_ba_30_ = lean_byte_array_push(v_ba_25_, v___x_29_);
v___x_31_ = 16u64;
v___x_32_ = lean_uint64_shift_right(v_v_21_, v___x_31_);
v___x_33_ = lean_uint64_land(v___x_32_, v___x_22_);
v___x_34_ = lean_uint64_to_uint8(v___x_33_);
v_ba_35_ = lean_byte_array_push(v_ba_30_, v___x_34_);
v___x_36_ = 24u64;
v___x_37_ = lean_uint64_shift_right(v_v_21_, v___x_36_);
v___x_38_ = lean_uint64_land(v___x_37_, v___x_22_);
v___x_39_ = lean_uint64_to_uint8(v___x_38_);
v_ba_40_ = lean_byte_array_push(v_ba_35_, v___x_39_);
v___x_41_ = 32u64;
v___x_42_ = lean_uint64_shift_right(v_v_21_, v___x_41_);
v___x_43_ = lean_uint64_land(v___x_42_, v___x_22_);
v___x_44_ = lean_uint64_to_uint8(v___x_43_);
v_ba_45_ = lean_byte_array_push(v_ba_40_, v___x_44_);
v___x_46_ = 40u64;
v___x_47_ = lean_uint64_shift_right(v_v_21_, v___x_46_);
v___x_48_ = lean_uint64_land(v___x_47_, v___x_22_);
v___x_49_ = lean_uint64_to_uint8(v___x_48_);
v_ba_50_ = lean_byte_array_push(v_ba_45_, v___x_49_);
v___x_51_ = 48u64;
v___x_52_ = lean_uint64_shift_right(v_v_21_, v___x_51_);
v___x_53_ = lean_uint64_land(v___x_52_, v___x_22_);
v___x_54_ = lean_uint64_to_uint8(v___x_53_);
v_ba_55_ = lean_byte_array_push(v_ba_50_, v___x_54_);
v___x_56_ = 56u64;
v___x_57_ = lean_uint64_shift_right(v_v_21_, v___x_56_);
v___x_58_ = lean_uint64_land(v___x_57_, v___x_22_);
v___x_59_ = lean_uint64_to_uint8(v___x_58_);
v___x_60_ = lean_byte_array_push(v_ba_55_, v___x_59_);
return v___x_60_;
}
#[no_mangle] pub unsafe extern "C" fn l_pushLE___boxed(mut v_ba_61_: *mut lean_object, mut v_v_62_: *mut lean_object) -> *mut lean_object{
let mut v_v_boxed_63_: u64 = 0; let mut v_res_64_: *mut lean_object = core::ptr::null_mut(); 
v_v_boxed_63_ = lean_unbox_uint64(v_v_62_);
lean_dec_ref(v_v_62_);
v_res_64_ = l_pushLE(v_ba_61_, v_v_boxed_63_);
return v_res_64_;
}
#[no_mangle] pub unsafe extern "C" fn l_readLE(mut v_ba_65_: *mut lean_object, mut v_off_66_: *mut lean_object) -> u64{
let mut v___x_67_: u8 = 0; let mut v___x_68_: u64 = 0; let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: u8 = 0; let mut v___x_72_: u64 = 0; let mut v___x_73_: u64 = 0; let mut v___x_74_: u64 = 0; let mut v___x_75_: u64 = 0; let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: u8 = 0; let mut v___x_79_: u64 = 0; let mut v___x_80_: u64 = 0; let mut v___x_81_: u64 = 0; let mut v___x_82_: u64 = 0; let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: u8 = 0; let mut v___x_86_: u64 = 0; let mut v___x_87_: u64 = 0; let mut v___x_88_: u64 = 0; let mut v___x_89_: u64 = 0; let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: u8 = 0; let mut v___x_93_: u64 = 0; let mut v___x_94_: u64 = 0; let mut v___x_95_: u64 = 0; let mut v___x_96_: u64 = 0; let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: u8 = 0; let mut v___x_100_: u64 = 0; let mut v___x_101_: u64 = 0; let mut v___x_102_: u64 = 0; let mut v___x_103_: u64 = 0; let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: u8 = 0; let mut v___x_107_: u64 = 0; let mut v___x_108_: u64 = 0; let mut v___x_109_: u64 = 0; let mut v___x_110_: u64 = 0; let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: u8 = 0; let mut v___x_114_: u64 = 0; let mut v___x_115_: u64 = 0; let mut v___x_116_: u64 = 0; let mut v___x_117_: u64 = 0; 
v___x_67_ = lean_byte_array_get(v_ba_65_, v_off_66_);
v___x_68_ = lean_uint8_to_uint64(v___x_67_);
v___x_69_ = lean_unsigned_to_nat(1);
v___x_70_ = lean_nat_add(v_off_66_, v___x_69_);
v___x_71_ = lean_byte_array_get(v_ba_65_, v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_uint8_to_uint64(v___x_71_);
v___x_73_ = 8u64;
v___x_74_ = lean_uint64_shift_left(v___x_72_, v___x_73_);
v___x_75_ = lean_uint64_add(v___x_68_, v___x_74_);
v___x_76_ = lean_unsigned_to_nat(2);
v___x_77_ = lean_nat_add(v_off_66_, v___x_76_);
v___x_78_ = lean_byte_array_get(v_ba_65_, v___x_77_);
lean_dec(v___x_77_);
v___x_79_ = lean_uint8_to_uint64(v___x_78_);
v___x_80_ = 16u64;
v___x_81_ = lean_uint64_shift_left(v___x_79_, v___x_80_);
v___x_82_ = lean_uint64_add(v___x_75_, v___x_81_);
v___x_83_ = lean_unsigned_to_nat(3);
v___x_84_ = lean_nat_add(v_off_66_, v___x_83_);
v___x_85_ = lean_byte_array_get(v_ba_65_, v___x_84_);
lean_dec(v___x_84_);
v___x_86_ = lean_uint8_to_uint64(v___x_85_);
v___x_87_ = 24u64;
v___x_88_ = lean_uint64_shift_left(v___x_86_, v___x_87_);
v___x_89_ = lean_uint64_add(v___x_82_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(4);
v___x_91_ = lean_nat_add(v_off_66_, v___x_90_);
v___x_92_ = lean_byte_array_get(v_ba_65_, v___x_91_);
lean_dec(v___x_91_);
v___x_93_ = lean_uint8_to_uint64(v___x_92_);
v___x_94_ = 32u64;
v___x_95_ = lean_uint64_shift_left(v___x_93_, v___x_94_);
v___x_96_ = lean_uint64_add(v___x_89_, v___x_95_);
v___x_97_ = lean_unsigned_to_nat(5);
v___x_98_ = lean_nat_add(v_off_66_, v___x_97_);
v___x_99_ = lean_byte_array_get(v_ba_65_, v___x_98_);
lean_dec(v___x_98_);
v___x_100_ = lean_uint8_to_uint64(v___x_99_);
v___x_101_ = 40u64;
v___x_102_ = lean_uint64_shift_left(v___x_100_, v___x_101_);
v___x_103_ = lean_uint64_add(v___x_96_, v___x_102_);
v___x_104_ = lean_unsigned_to_nat(6);
v___x_105_ = lean_nat_add(v_off_66_, v___x_104_);
v___x_106_ = lean_byte_array_get(v_ba_65_, v___x_105_);
lean_dec(v___x_105_);
v___x_107_ = lean_uint8_to_uint64(v___x_106_);
v___x_108_ = 48u64;
v___x_109_ = lean_uint64_shift_left(v___x_107_, v___x_108_);
v___x_110_ = lean_uint64_add(v___x_103_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(7);
v___x_112_ = lean_nat_add(v_off_66_, v___x_111_);
v___x_113_ = lean_byte_array_get(v_ba_65_, v___x_112_);
lean_dec(v___x_112_);
v___x_114_ = lean_uint8_to_uint64(v___x_113_);
v___x_115_ = 56u64;
v___x_116_ = lean_uint64_shift_left(v___x_114_, v___x_115_);
v___x_117_ = lean_uint64_add(v___x_110_, v___x_116_);
return v___x_117_;
}
#[no_mangle] pub unsafe extern "C" fn l_readLE___boxed(mut v_ba_118_: *mut lean_object, mut v_off_119_: *mut lean_object) -> *mut lean_object{
let mut v_res_120_: u64 = 0; let mut v_r_121_: *mut lean_object = core::ptr::null_mut(); 
v_res_120_ = l_readLE(v_ba_118_, v_off_119_);
lean_dec(v_off_119_);
lean_dec_ref(v_ba_118_);
v_r_121_ = lean_box_uint64(v_res_120_);
return v_r_121_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_timeS___redArg___closed__0() -> f64{
let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: u8 = 0; let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: f64 = 0.0; 
v___x_122_ = lean_unsigned_to_nat(1);
v___x_123_ = 1;
v___x_124_ = lean_unsigned_to_nat(10000);
v___x_125_ = l_Float_ofScientific(v___x_124_, v___x_123_, v___x_122_);
return v___x_125_;
}
#[no_mangle] pub unsafe extern "C" fn l_timeS___redArg(mut v_act_126_: *mut lean_object) -> *mut lean_object{
let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); let mut v_a_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_133_: u8 = 0; let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: f64 = 0.0; let mut v___x_137_: f64 = 0.0; let mut v___x_138_: f64 = 0.0; let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_143_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_144_: u8 = 0; let mut v_a_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_148_: u8 = 0; let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_151_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_152_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_128_ = lean_io_mono_ms_now();
v___x_129_ = lean_apply_1(v_act_126_, lean_box(0));
if lean_obj_tag(v___x_129_) == 0 {
let mut v_a_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_133_: u8 = 0; let mut v_isSharedCheck_144_: u8 = 0; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_144_ = (!lean_is_exclusive(v___x_129_)) as u8;
if v_isSharedCheck_144_ == 0 {
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_144_;
state = 1; continue;
} else {
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_144_;
state = 1; continue;
}
} else {
let mut v_a_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_148_: u8 = 0; let mut v_isSharedCheck_152_: u8 = 0; 
lean_dec(v___x_128_);
v_a_145_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_152_ = (!lean_is_exclusive(v___x_129_)) as u8;
if v_isSharedCheck_152_ == 0 {
v___x_147_ = v___x_129_;
v_isShared_148_ = v_isSharedCheck_152_;
state = 3; continue;
} else {
lean_inc(v_a_145_);
lean_dec(v___x_129_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
state = 3; continue;
}
}
}
1 => {
v___x_134_ = lean_io_mono_ms_now();
v___x_135_ = lean_nat_sub(v___x_134_, v___x_128_);
lean_dec(v___x_128_);
lean_dec(v___x_134_);
v___x_136_ = lean_float_of_nat(v___x_135_);
v___x_137_ = lean_float_once(core::ptr::addr_of_mut!(l_timeS___redArg___closed__0), core::ptr::addr_of_mut!(l_timeS___redArg___closed__0_once), _init_l_timeS___redArg___closed__0);
v___x_138_ = lean_float_div(v___x_136_, v___x_137_);
v___x_139_ = lean_box_float(v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_140_, 0, v_a_130_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
if v_isShared_133_ == 0 {
lean_ctor_set(v___x_132_, 0, v___x_140_);
v___x_142_ = v___x_132_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_143_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
state = 2; continue;
}
}
3 => {
if v_isShared_148_ == 0 {
v___x_150_ = v___x_147_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_151_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_timeS___redArg___boxed(mut v_act_153_: *mut lean_object, mut v_a_154_: *mut lean_object) -> *mut lean_object{
let mut v_res_155_: *mut lean_object = core::ptr::null_mut(); 
v_res_155_ = l_timeS___redArg(v_act_153_);
return v_res_155_;
}
#[no_mangle] pub unsafe extern "C" fn l_timeS(mut v_00_u03b1_156_: *mut lean_object, mut v_act_157_: *mut lean_object) -> *mut lean_object{
let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); 
v___x_159_ = l_timeS___redArg(v_act_157_);
return v___x_159_;
}
#[no_mangle] pub unsafe extern "C" fn l_timeS___boxed(mut v_00_u03b1_160_: *mut lean_object, mut v_act_161_: *mut lean_object, mut v_a_162_: *mut lean_object) -> *mut lean_object{
let mut v_res_163_: *mut lean_object = core::ptr::null_mut(); 
v_res_163_ = l_timeS(v_00_u03b1_160_, v_act_161_);
return v_res_163_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__0___redArg(mut v_range_164_: *mut lean_object, mut v_b_165_: *mut lean_object, mut v_i_166_: *mut lean_object) -> *mut lean_object{
let mut v_stop_168_: *mut lean_object = core::ptr::null_mut(); let mut v_step_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: u8 = 0; let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_172_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_176_: u8 = 0; let mut v___x_177_: u64 = 0; let mut v___x_178_: u64 = 0; let mut v___x_179_: u64 = 0; let mut v___x_180_: u64 = 0; let mut v_x_181_: u64 = 0; let mut v___x_182_: u64 = 0; let mut v___x_183_: u64 = 0; let mut v_x_184_: u64 = 0; let mut v___x_185_: u64 = 0; let mut v___x_186_: u64 = 0; let mut v_x_187_: u64 = 0; let mut v___x_188_: u64 = 0; let mut v___x_189_: u64 = 0; let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); let mut v___x_195_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_197_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_198_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_stop_168_ = lean_ctor_get(v_range_164_, 1);
v_step_169_ = lean_ctor_get(v_range_164_, 2);
v___x_170_ = lean_nat_dec_lt(v_i_166_, v_stop_168_);
if v___x_170_ == 0 {
let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_166_);
v___x_171_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_171_, 0, v_b_165_);
return v___x_171_;
} else {
let mut v_fst_172_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_176_: u8 = 0; let mut v_isSharedCheck_198_: u8 = 0; 
v_fst_172_ = lean_ctor_get(v_b_165_, 0);
v_snd_173_ = lean_ctor_get(v_b_165_, 1);
v_isSharedCheck_198_ = (!lean_is_exclusive(v_b_165_)) as u8;
if v_isSharedCheck_198_ == 0 {
v___x_175_ = v_b_165_;
v_isShared_176_ = v_isSharedCheck_198_;
state = 1; continue;
} else {
lean_inc(v_snd_173_);
lean_inc(v_fst_172_);
lean_dec(v_b_165_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_198_;
state = 1; continue;
}
}
}
1 => {
v___x_177_ = 12u64;
v___x_178_ = lean_unbox_uint64(v_fst_172_);
v___x_179_ = lean_uint64_shift_right(v___x_178_, v___x_177_);
v___x_180_ = lean_unbox_uint64(v_fst_172_);
lean_dec(v_fst_172_);
v_x_181_ = lean_uint64_xor(v___x_180_, v___x_179_);
v___x_182_ = 25u64;
v___x_183_ = lean_uint64_shift_left(v_x_181_, v___x_182_);
v_x_184_ = lean_uint64_xor(v_x_181_, v___x_183_);
v___x_185_ = 27u64;
v___x_186_ = lean_uint64_shift_right(v_x_184_, v___x_185_);
v_x_187_ = lean_uint64_xor(v_x_184_, v___x_186_);
v___x_188_ = 2685821657736338717u64;
v___x_189_ = lean_uint64_mul(v_x_187_, v___x_188_);
v___x_190_ = lean_box_uint64(v___x_189_);
v___x_191_ = lean_array_push(v_snd_173_, v___x_190_);
v___x_192_ = lean_box_uint64(v_x_187_);
if v_isShared_176_ == 0 {
lean_ctor_set(v___x_175_, 1, v___x_191_);
lean_ctor_set(v___x_175_, 0, v___x_192_);
v___x_194_ = v___x_175_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_197_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_191_);
v___x_194_ = v_reuseFailAlloc_197_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__0___redArg___boxed(mut v_range_199_: *mut lean_object, mut v_b_200_: *mut lean_object, mut v_i_201_: *mut lean_object, mut v___y_202_: *mut lean_object) -> *mut lean_object{
let mut v_res_203_: *mut lean_object = core::ptr::null_mut(); 
v_res_203_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__0___redArg(v_range_199_, v_b_200_, v_i_201_);
lean_dec_ref(v_range_199_);
return v_res_203_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1_spec__2___redArg(mut v_hi_204_: *mut lean_object, mut v_pivot_205_: u64, mut v_as_206_: *mut lean_object, mut v_i_207_: *mut lean_object, mut v_k_208_: *mut lean_object) -> *mut lean_object{
let mut v___x_209_: u8 = 0; let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: u64 = 0; let mut v___x_214_: u8 = 0; let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_209_ = lean_nat_dec_lt(v_k_208_, v_hi_204_);
if v___x_209_ == 0 {
let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_k_208_);
v___x_210_ = lean_array_fswap(v_as_206_, v_i_207_, v_hi_204_);
v___x_211_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_211_, 0, v_i_207_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
return v___x_211_;
} else {
let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: u64 = 0; let mut v___x_214_: u8 = 0; 
v___x_212_ = lean_array_fget_borrowed(v_as_206_, v_k_208_);
v___x_213_ = lean_unbox_uint64(v___x_212_);
v___x_214_ = lean_uint64_dec_lt(v___x_213_, v_pivot_205_);
if v___x_214_ == 0 {
let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); 
v___x_215_ = lean_unsigned_to_nat(1);
v___x_216_ = lean_nat_add(v_k_208_, v___x_215_);
lean_dec(v_k_208_);
v_k_208_ = v___x_216_;
state = 0; continue;
} else {
let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); 
v___x_218_ = lean_array_fswap(v_as_206_, v_i_207_, v_k_208_);
v___x_219_ = lean_unsigned_to_nat(1);
v___x_220_ = lean_nat_add(v_i_207_, v___x_219_);
lean_dec(v_i_207_);
v___x_221_ = lean_nat_add(v_k_208_, v___x_219_);
lean_dec(v_k_208_);
v_as_206_ = v___x_218_;
v_i_207_ = v___x_220_;
v_k_208_ = v___x_221_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1_spec__2___redArg___boxed(mut v_hi_223_: *mut lean_object, mut v_pivot_224_: *mut lean_object, mut v_as_225_: *mut lean_object, mut v_i_226_: *mut lean_object, mut v_k_227_: *mut lean_object) -> *mut lean_object{
let mut v_pivot_boxed_228_: u64 = 0; let mut v_res_229_: *mut lean_object = core::ptr::null_mut(); 
v_pivot_boxed_228_ = lean_unbox_uint64(v_pivot_224_);
lean_dec_ref(v_pivot_224_);
v_res_229_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1_spec__2___redArg(v_hi_223_, v_pivot_boxed_228_, v_as_225_, v_i_226_, v_k_227_);
lean_dec(v_hi_223_);
return v_res_229_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1___redArg(mut v_n_230_: *mut lean_object, mut v_as_231_: *mut lean_object, mut v_lo_232_: *mut lean_object, mut v_hi_233_: *mut lean_object) -> *mut lean_object{
let mut v___y_235_: *mut lean_object = core::ptr::null_mut(); let mut v_pivot_236_: *mut lean_object = core::ptr::null_mut(); let mut v___x_237_: u64 = 0; let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_239_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_241_: u8 = 0; let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_246_: u8 = 0; let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); let mut v_mid_249_: *mut lean_object = core::ptr::null_mut(); let mut v___y_251_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: *mut lean_object = core::ptr::null_mut(); let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254_: u64 = 0; let mut v___x_255_: u64 = 0; let mut v___x_256_: u8 = 0; let mut v___x_257_: *mut lean_object = core::ptr::null_mut(); let mut v___y_259_: *mut lean_object = core::ptr::null_mut(); let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_261_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: u64 = 0; let mut v___x_263_: u64 = 0; let mut v___x_264_: u8 = 0; let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: u64 = 0; let mut v___x_269_: u64 = 0; let mut v___x_270_: u8 = 0; let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_246_ = lean_nat_dec_lt(v_lo_232_, v_hi_233_);
if v___x_246_ == 0 {
lean_dec(v_lo_232_);
return v_as_231_;
} else {
let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); let mut v_mid_249_: *mut lean_object = core::ptr::null_mut(); let mut v___y_251_: *mut lean_object = core::ptr::null_mut(); let mut v___y_259_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: u64 = 0; let mut v___x_269_: u64 = 0; let mut v___x_270_: u8 = 0; 
v___x_247_ = lean_nat_add(v_lo_232_, v_hi_233_);
v___x_248_ = lean_unsigned_to_nat(1);
v_mid_249_ = lean_nat_shiftr(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
v___x_266_ = lean_array_fget_borrowed(v_as_231_, v_mid_249_);
v___x_267_ = lean_array_fget_borrowed(v_as_231_, v_lo_232_);
v___x_268_ = lean_unbox_uint64(v___x_266_);
v___x_269_ = lean_unbox_uint64(v___x_267_);
v___x_270_ = lean_uint64_dec_lt(v___x_268_, v___x_269_);
if v___x_270_ == 0 {
v___y_259_ = v_as_231_;
state = 3; continue;
} else {
let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); 
v___x_271_ = lean_array_fswap(v_as_231_, v_lo_232_, v_mid_249_);
v___y_259_ = v___x_271_;
state = 3; continue;
}
}
}
1 => {
v_pivot_236_ = lean_array_fget_borrowed(v___y_235_, v_hi_233_);
v___x_237_ = lean_unbox_uint64(v_pivot_236_);
lean_inc_n(v_lo_232_, 2);
v___x_238_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1_spec__2___redArg(v_hi_233_, v___x_237_, v___y_235_, v_lo_232_, v_lo_232_);
v_fst_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_fst_239_);
v_snd_240_ = lean_ctor_get(v___x_238_, 1);
lean_inc(v_snd_240_);
lean_dec_ref(v___x_238_);
v___x_241_ = lean_nat_dec_le(v_hi_233_, v_fst_239_);
if v___x_241_ == 0 {
let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); 
v___x_242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1___redArg(v_n_230_, v_snd_240_, v_lo_232_, v_fst_239_);
v___x_243_ = lean_unsigned_to_nat(1);
v___x_244_ = lean_nat_add(v_fst_239_, v___x_243_);
lean_dec(v_fst_239_);
v_as_231_ = v___x_242_;
v_lo_232_ = v___x_244_;
state = 0; continue;
} else {
lean_dec(v_fst_239_);
lean_dec(v_lo_232_);
return v_snd_240_;
}
}
2 => {
v___x_252_ = lean_array_fget_borrowed(v___y_251_, v_mid_249_);
v___x_253_ = lean_array_fget_borrowed(v___y_251_, v_hi_233_);
v___x_254_ = lean_unbox_uint64(v___x_252_);
v___x_255_ = lean_unbox_uint64(v___x_253_);
v___x_256_ = lean_uint64_dec_lt(v___x_254_, v___x_255_);
if v___x_256_ == 0 {
lean_dec(v_mid_249_);
v___y_235_ = v___y_251_;
state = 1; continue;
} else {
let mut v___x_257_: *mut lean_object = core::ptr::null_mut(); 
v___x_257_ = lean_array_fswap(v___y_251_, v_mid_249_, v_hi_233_);
lean_dec(v_mid_249_);
v___y_235_ = v___x_257_;
state = 1; continue;
}
}
3 => {
v___x_260_ = lean_array_fget_borrowed(v___y_259_, v_hi_233_);
v___x_261_ = lean_array_fget_borrowed(v___y_259_, v_lo_232_);
v___x_262_ = lean_unbox_uint64(v___x_260_);
v___x_263_ = lean_unbox_uint64(v___x_261_);
v___x_264_ = lean_uint64_dec_lt(v___x_262_, v___x_263_);
if v___x_264_ == 0 {
v___y_251_ = v___y_259_;
state = 2; continue;
} else {
let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); 
v___x_265_ = lean_array_fswap(v___y_259_, v_lo_232_, v_hi_233_);
v___y_251_ = v___x_265_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1___redArg___boxed(mut v_n_272_: *mut lean_object, mut v_as_273_: *mut lean_object, mut v_lo_274_: *mut lean_object, mut v_hi_275_: *mut lean_object) -> *mut lean_object{
let mut v_res_276_: *mut lean_object = core::ptr::null_mut(); 
v_res_276_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1___redArg(v_n_272_, v_as_273_, v_lo_274_, v_hi_275_);
lean_dec(v_hi_275_);
lean_dec(v_n_272_);
return v_res_276_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_qsortOrd___at___00main_spec__1(mut v_xs_277_: *mut lean_object) -> *mut lean_object{
let mut v___x_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_279_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: u8 = 0; let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); let mut v___y_284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_285_: u8 = 0; let mut v___x_286_: *mut lean_object = core::ptr::null_mut(); let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_278_ = lean_array_get_size(v_xs_277_);
v___x_279_ = lean_unsigned_to_nat(0);
v___x_280_ = lean_nat_dec_eq(v___x_278_, v___x_279_);
if v___x_280_ == 0 {
let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); let mut v___y_284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: u8 = 0; 
v___x_281_ = lean_unsigned_to_nat(1);
v___x_282_ = lean_nat_sub(v___x_278_, v___x_281_);
v___x_288_ = lean_nat_dec_le(v___x_279_, v___x_282_);
if v___x_288_ == 0 {
lean_inc(v___x_282_);
v___y_284_ = v___x_282_;
state = 1; continue;
} else {
v___y_284_ = v___x_279_;
state = 1; continue;
}
} else {
return v_xs_277_;
}
}
1 => {
v___x_285_ = lean_nat_dec_le(v___y_284_, v___x_282_);
if v___x_285_ == 0 {
let mut v___x_286_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_282_);
lean_inc(v___y_284_);
v___x_286_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1___redArg(v___x_278_, v_xs_277_, v___y_284_, v___y_284_);
lean_dec(v___y_284_);
return v___x_286_;
} else {
let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); 
v___x_287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1___redArg(v___x_278_, v_xs_277_, v___y_284_, v___x_282_);
lean_dec(v___x_282_);
return v___x_287_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v___x_289_: *mut lean_object, mut v___x_290_: *mut lean_object, mut v___x_291_: *mut lean_object) -> *mut lean_object{
let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v_a_294_: *mut lean_object = core::ptr::null_mut(); let mut v___x_296_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_297_: u8 = 0; let mut v_snd_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_302_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_303_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_293_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__0___redArg(v___x_289_, v___x_290_, v___x_291_);
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_303_ = (!lean_is_exclusive(v___x_293_)) as u8;
if v_isSharedCheck_303_ == 0 {
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_303_;
state = 1; continue;
} else {
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_303_;
state = 1; continue;
}
}
1 => {
v_snd_298_ = lean_ctor_get(v_a_294_, 1);
lean_inc(v_snd_298_);
lean_dec(v_a_294_);
v___x_299_ = l_Array_qsortOrd___at___00main_spec__1(v_snd_298_);
if v_isShared_297_ == 0 {
lean_ctor_set(v___x_296_, 0, v___x_299_);
v___x_301_ = v___x_296_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_302_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0___boxed(mut v___x_304_: *mut lean_object, mut v___x_305_: *mut lean_object, mut v___x_306_: *mut lean_object, mut v___y_307_: *mut lean_object) -> *mut lean_object{
let mut v_res_308_: *mut lean_object = core::ptr::null_mut(); 
v_res_308_ = l_main___lam__0(v___x_304_, v___x_305_, v___x_306_);
lean_dec_ref(v___x_304_);
return v_res_308_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed__const__1() -> *mut lean_object{
let mut v___x_309_: u64 = 0; let mut v___x_310_: *mut lean_object = core::ptr::null_mut(); 
v___x_309_ = l_instInhabitedUInt64;
v___x_310_ = lean_box_uint64(v___x_309_);
return v___x_310_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(mut v_fst_311_: *mut lean_object, mut v_range_312_: *mut lean_object, mut v_b_313_: *mut lean_object, mut v_i_314_: *mut lean_object) -> *mut lean_object{
let mut v_stop_316_: *mut lean_object = core::ptr::null_mut(); let mut v_step_317_: *mut lean_object = core::ptr::null_mut(); let mut v___x_318_: u8 = 0; let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); let mut v___x_320_: *mut lean_object = core::ptr::null_mut(); let mut v___x_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_322_: u64 = 0; let mut v___x_323_: u64 = 0; let mut v___x_324_: u64 = 0; let mut v___x_325_: u8 = 0; let mut v_ba_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: u64 = 0; let mut v___x_328_: u64 = 0; let mut v___x_329_: u64 = 0; let mut v___x_330_: u64 = 0; let mut v___x_331_: u8 = 0; let mut v_ba_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: u64 = 0; let mut v___x_334_: u64 = 0; let mut v___x_335_: u64 = 0; let mut v___x_336_: u64 = 0; let mut v___x_337_: u8 = 0; let mut v_ba_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: u64 = 0; let mut v___x_340_: u64 = 0; let mut v___x_341_: u64 = 0; let mut v___x_342_: u64 = 0; let mut v___x_343_: u8 = 0; let mut v_ba_344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_345_: u64 = 0; let mut v___x_346_: u64 = 0; let mut v___x_347_: u64 = 0; let mut v___x_348_: u64 = 0; let mut v___x_349_: u8 = 0; let mut v_ba_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: u64 = 0; let mut v___x_352_: u64 = 0; let mut v___x_353_: u64 = 0; let mut v___x_354_: u64 = 0; let mut v___x_355_: u8 = 0; let mut v_ba_356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_357_: u64 = 0; let mut v___x_358_: u64 = 0; let mut v___x_359_: u64 = 0; let mut v___x_360_: u64 = 0; let mut v___x_361_: u8 = 0; let mut v_ba_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: u64 = 0; let mut v___x_364_: u64 = 0; let mut v___x_365_: u64 = 0; let mut v___x_366_: u64 = 0; let mut v___x_367_: u8 = 0; let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_stop_316_ = lean_ctor_get(v_range_312_, 1);
v_step_317_ = lean_ctor_get(v_range_312_, 2);
v___x_318_ = lean_nat_dec_lt(v_i_314_, v_stop_316_);
if v___x_318_ == 0 {
let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_314_);
v___x_319_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_319_, 0, v_b_313_);
return v___x_319_;
} else {
let mut v___x_320_: *mut lean_object = core::ptr::null_mut(); let mut v___x_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_322_: u64 = 0; let mut v___x_323_: u64 = 0; let mut v___x_324_: u64 = 0; let mut v___x_325_: u8 = 0; let mut v_ba_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: u64 = 0; let mut v___x_328_: u64 = 0; let mut v___x_329_: u64 = 0; let mut v___x_330_: u64 = 0; let mut v___x_331_: u8 = 0; let mut v_ba_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: u64 = 0; let mut v___x_334_: u64 = 0; let mut v___x_335_: u64 = 0; let mut v___x_336_: u64 = 0; let mut v___x_337_: u8 = 0; let mut v_ba_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: u64 = 0; let mut v___x_340_: u64 = 0; let mut v___x_341_: u64 = 0; let mut v___x_342_: u64 = 0; let mut v___x_343_: u8 = 0; let mut v_ba_344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_345_: u64 = 0; let mut v___x_346_: u64 = 0; let mut v___x_347_: u64 = 0; let mut v___x_348_: u64 = 0; let mut v___x_349_: u8 = 0; let mut v_ba_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: u64 = 0; let mut v___x_352_: u64 = 0; let mut v___x_353_: u64 = 0; let mut v___x_354_: u64 = 0; let mut v___x_355_: u8 = 0; let mut v_ba_356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_357_: u64 = 0; let mut v___x_358_: u64 = 0; let mut v___x_359_: u64 = 0; let mut v___x_360_: u64 = 0; let mut v___x_361_: u8 = 0; let mut v_ba_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: u64 = 0; let mut v___x_364_: u64 = 0; let mut v___x_365_: u64 = 0; let mut v___x_366_: u64 = 0; let mut v___x_367_: u8 = 0; let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); 
v___x_320_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed__const__1;
v___x_321_ = lean_array_get_borrowed(v___x_320_, v_fst_311_, v_i_314_);
v___x_322_ = 255u64;
v___x_323_ = lean_unbox_uint64(v___x_321_);
v___x_324_ = lean_uint64_land(v___x_323_, v___x_322_);
v___x_325_ = lean_uint64_to_uint8(v___x_324_);
v_ba_326_ = lean_byte_array_push(v_b_313_, v___x_325_);
v___x_327_ = 8u64;
v___x_328_ = lean_unbox_uint64(v___x_321_);
v___x_329_ = lean_uint64_shift_right(v___x_328_, v___x_327_);
v___x_330_ = lean_uint64_land(v___x_329_, v___x_322_);
v___x_331_ = lean_uint64_to_uint8(v___x_330_);
v_ba_332_ = lean_byte_array_push(v_ba_326_, v___x_331_);
v___x_333_ = 16u64;
v___x_334_ = lean_unbox_uint64(v___x_321_);
v___x_335_ = lean_uint64_shift_right(v___x_334_, v___x_333_);
v___x_336_ = lean_uint64_land(v___x_335_, v___x_322_);
v___x_337_ = lean_uint64_to_uint8(v___x_336_);
v_ba_338_ = lean_byte_array_push(v_ba_332_, v___x_337_);
v___x_339_ = 24u64;
v___x_340_ = lean_unbox_uint64(v___x_321_);
v___x_341_ = lean_uint64_shift_right(v___x_340_, v___x_339_);
v___x_342_ = lean_uint64_land(v___x_341_, v___x_322_);
v___x_343_ = lean_uint64_to_uint8(v___x_342_);
v_ba_344_ = lean_byte_array_push(v_ba_338_, v___x_343_);
v___x_345_ = 32u64;
v___x_346_ = lean_unbox_uint64(v___x_321_);
v___x_347_ = lean_uint64_shift_right(v___x_346_, v___x_345_);
v___x_348_ = lean_uint64_land(v___x_347_, v___x_322_);
v___x_349_ = lean_uint64_to_uint8(v___x_348_);
v_ba_350_ = lean_byte_array_push(v_ba_344_, v___x_349_);
v___x_351_ = 40u64;
v___x_352_ = lean_unbox_uint64(v___x_321_);
v___x_353_ = lean_uint64_shift_right(v___x_352_, v___x_351_);
v___x_354_ = lean_uint64_land(v___x_353_, v___x_322_);
v___x_355_ = lean_uint64_to_uint8(v___x_354_);
v_ba_356_ = lean_byte_array_push(v_ba_350_, v___x_355_);
v___x_357_ = 48u64;
v___x_358_ = lean_unbox_uint64(v___x_321_);
v___x_359_ = lean_uint64_shift_right(v___x_358_, v___x_357_);
v___x_360_ = lean_uint64_land(v___x_359_, v___x_322_);
v___x_361_ = lean_uint64_to_uint8(v___x_360_);
v_ba_362_ = lean_byte_array_push(v_ba_356_, v___x_361_);
v___x_363_ = 56u64;
v___x_364_ = lean_unbox_uint64(v___x_321_);
v___x_365_ = lean_uint64_shift_right(v___x_364_, v___x_363_);
v___x_366_ = lean_uint64_land(v___x_365_, v___x_322_);
v___x_367_ = lean_uint64_to_uint8(v___x_366_);
v___x_368_ = lean_byte_array_push(v_ba_362_, v___x_367_);
v___x_369_ = lean_nat_add(v_i_314_, v_step_317_);
lean_dec(v_i_314_);
v_b_313_ = v___x_368_;
v_i_314_ = v___x_369_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed(mut v_fst_371_: *mut lean_object, mut v_range_372_: *mut lean_object, mut v_b_373_: *mut lean_object, mut v_i_374_: *mut lean_object, mut v___y_375_: *mut lean_object) -> *mut lean_object{
let mut v_res_376_: *mut lean_object = core::ptr::null_mut(); 
v_res_376_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(v_fst_371_, v_range_372_, v_b_373_, v_i_374_);
lean_dec_ref(v_range_372_);
lean_dec_ref(v_fst_371_);
return v_res_376_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__1(mut v_fst_377_: *mut lean_object, mut v___x_378_: *mut lean_object, mut v___x_379_: *mut lean_object, mut v___x_380_: *mut lean_object, mut v_snd_381_: *mut lean_object) -> *mut lean_object{
let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v_a_384_: *mut lean_object = core::ptr::null_mut(); let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); 
v___x_383_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(v_fst_377_, v___x_378_, v___x_379_, v___x_380_);
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v___x_383_);
v___x_385_ = l_IO_FS_writeBinFile(v_snd_381_, v_a_384_);
lean_dec(v_a_384_);
return v___x_385_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__1___boxed(mut v_fst_386_: *mut lean_object, mut v___x_387_: *mut lean_object, mut v___x_388_: *mut lean_object, mut v___x_389_: *mut lean_object, mut v_snd_390_: *mut lean_object, mut v___y_391_: *mut lean_object) -> *mut lean_object{
let mut v_res_392_: *mut lean_object = core::ptr::null_mut(); 
v_res_392_ = l_main___lam__1(v_fst_386_, v___x_387_, v___x_388_, v___x_389_, v_snd_390_);
lean_dec_ref(v_snd_390_);
lean_dec_ref(v___x_387_);
lean_dec_ref(v_fst_386_);
return v_res_392_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(mut v_a_393_: *mut lean_object, mut v_range_394_: *mut lean_object, mut v_b_395_: *mut lean_object, mut v_i_396_: *mut lean_object) -> *mut lean_object{
let mut v_stop_398_: *mut lean_object = core::ptr::null_mut(); let mut v_step_399_: *mut lean_object = core::ptr::null_mut(); let mut v___x_400_: u8 = 0; let mut v___x_401_: *mut lean_object = core::ptr::null_mut(); let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: u8 = 0; let mut v___x_405_: u64 = 0; let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: u8 = 0; let mut v___x_409_: u64 = 0; let mut v___x_410_: u64 = 0; let mut v___x_411_: u64 = 0; let mut v___x_412_: u64 = 0; let mut v___x_413_: *mut lean_object = core::ptr::null_mut(); let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); let mut v___x_415_: u8 = 0; let mut v___x_416_: u64 = 0; let mut v___x_417_: u64 = 0; let mut v___x_418_: u64 = 0; let mut v___x_419_: u64 = 0; let mut v___x_420_: *mut lean_object = core::ptr::null_mut(); let mut v___x_421_: *mut lean_object = core::ptr::null_mut(); let mut v___x_422_: u8 = 0; let mut v___x_423_: u64 = 0; let mut v___x_424_: u64 = 0; let mut v___x_425_: u64 = 0; let mut v___x_426_: u64 = 0; let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: u8 = 0; let mut v___x_430_: u64 = 0; let mut v___x_431_: u64 = 0; let mut v___x_432_: u64 = 0; let mut v___x_433_: u64 = 0; let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_436_: u8 = 0; let mut v___x_437_: u64 = 0; let mut v___x_438_: u64 = 0; let mut v___x_439_: u64 = 0; let mut v___x_440_: u64 = 0; let mut v___x_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v___x_443_: u8 = 0; let mut v___x_444_: u64 = 0; let mut v___x_445_: u64 = 0; let mut v___x_446_: u64 = 0; let mut v___x_447_: u64 = 0; let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: u8 = 0; let mut v___x_451_: u64 = 0; let mut v___x_452_: u64 = 0; let mut v___x_453_: u64 = 0; let mut v___x_454_: u64 = 0; let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_stop_398_ = lean_ctor_get(v_range_394_, 1);
v_step_399_ = lean_ctor_get(v_range_394_, 2);
v___x_400_ = lean_nat_dec_lt(v_i_396_, v_stop_398_);
if v___x_400_ == 0 {
let mut v___x_401_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_396_);
v___x_401_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_401_, 0, v_b_395_);
return v___x_401_;
} else {
let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: u8 = 0; let mut v___x_405_: u64 = 0; let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: u8 = 0; let mut v___x_409_: u64 = 0; let mut v___x_410_: u64 = 0; let mut v___x_411_: u64 = 0; let mut v___x_412_: u64 = 0; let mut v___x_413_: *mut lean_object = core::ptr::null_mut(); let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); let mut v___x_415_: u8 = 0; let mut v___x_416_: u64 = 0; let mut v___x_417_: u64 = 0; let mut v___x_418_: u64 = 0; let mut v___x_419_: u64 = 0; let mut v___x_420_: *mut lean_object = core::ptr::null_mut(); let mut v___x_421_: *mut lean_object = core::ptr::null_mut(); let mut v___x_422_: u8 = 0; let mut v___x_423_: u64 = 0; let mut v___x_424_: u64 = 0; let mut v___x_425_: u64 = 0; let mut v___x_426_: u64 = 0; let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: u8 = 0; let mut v___x_430_: u64 = 0; let mut v___x_431_: u64 = 0; let mut v___x_432_: u64 = 0; let mut v___x_433_: u64 = 0; let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_436_: u8 = 0; let mut v___x_437_: u64 = 0; let mut v___x_438_: u64 = 0; let mut v___x_439_: u64 = 0; let mut v___x_440_: u64 = 0; let mut v___x_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v___x_443_: u8 = 0; let mut v___x_444_: u64 = 0; let mut v___x_445_: u64 = 0; let mut v___x_446_: u64 = 0; let mut v___x_447_: u64 = 0; let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: u8 = 0; let mut v___x_451_: u64 = 0; let mut v___x_452_: u64 = 0; let mut v___x_453_: u64 = 0; let mut v___x_454_: u64 = 0; let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); 
v___x_402_ = lean_unsigned_to_nat(8);
v___x_403_ = lean_nat_mul(v_i_396_, v___x_402_);
v___x_404_ = lean_byte_array_get(v_a_393_, v___x_403_);
v___x_405_ = lean_uint8_to_uint64(v___x_404_);
v___x_406_ = lean_unsigned_to_nat(1);
v___x_407_ = lean_nat_add(v___x_403_, v___x_406_);
v___x_408_ = lean_byte_array_get(v_a_393_, v___x_407_);
lean_dec(v___x_407_);
v___x_409_ = lean_uint8_to_uint64(v___x_408_);
v___x_410_ = 8u64;
v___x_411_ = lean_uint64_shift_left(v___x_409_, v___x_410_);
v___x_412_ = lean_uint64_add(v___x_405_, v___x_411_);
v___x_413_ = lean_unsigned_to_nat(2);
v___x_414_ = lean_nat_add(v___x_403_, v___x_413_);
v___x_415_ = lean_byte_array_get(v_a_393_, v___x_414_);
lean_dec(v___x_414_);
v___x_416_ = lean_uint8_to_uint64(v___x_415_);
v___x_417_ = 16u64;
v___x_418_ = lean_uint64_shift_left(v___x_416_, v___x_417_);
v___x_419_ = lean_uint64_add(v___x_412_, v___x_418_);
v___x_420_ = lean_unsigned_to_nat(3);
v___x_421_ = lean_nat_add(v___x_403_, v___x_420_);
v___x_422_ = lean_byte_array_get(v_a_393_, v___x_421_);
lean_dec(v___x_421_);
v___x_423_ = lean_uint8_to_uint64(v___x_422_);
v___x_424_ = 24u64;
v___x_425_ = lean_uint64_shift_left(v___x_423_, v___x_424_);
v___x_426_ = lean_uint64_add(v___x_419_, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(4);
v___x_428_ = lean_nat_add(v___x_403_, v___x_427_);
v___x_429_ = lean_byte_array_get(v_a_393_, v___x_428_);
lean_dec(v___x_428_);
v___x_430_ = lean_uint8_to_uint64(v___x_429_);
v___x_431_ = 32u64;
v___x_432_ = lean_uint64_shift_left(v___x_430_, v___x_431_);
v___x_433_ = lean_uint64_add(v___x_426_, v___x_432_);
v___x_434_ = lean_unsigned_to_nat(5);
v___x_435_ = lean_nat_add(v___x_403_, v___x_434_);
v___x_436_ = lean_byte_array_get(v_a_393_, v___x_435_);
lean_dec(v___x_435_);
v___x_437_ = lean_uint8_to_uint64(v___x_436_);
v___x_438_ = 40u64;
v___x_439_ = lean_uint64_shift_left(v___x_437_, v___x_438_);
v___x_440_ = lean_uint64_add(v___x_433_, v___x_439_);
v___x_441_ = lean_unsigned_to_nat(6);
v___x_442_ = lean_nat_add(v___x_403_, v___x_441_);
v___x_443_ = lean_byte_array_get(v_a_393_, v___x_442_);
lean_dec(v___x_442_);
v___x_444_ = lean_uint8_to_uint64(v___x_443_);
v___x_445_ = 48u64;
v___x_446_ = lean_uint64_shift_left(v___x_444_, v___x_445_);
v___x_447_ = lean_uint64_add(v___x_440_, v___x_446_);
v___x_448_ = lean_unsigned_to_nat(7);
v___x_449_ = lean_nat_add(v___x_403_, v___x_448_);
lean_dec(v___x_403_);
v___x_450_ = lean_byte_array_get(v_a_393_, v___x_449_);
lean_dec(v___x_449_);
v___x_451_ = lean_uint8_to_uint64(v___x_450_);
v___x_452_ = 56u64;
v___x_453_ = lean_uint64_shift_left(v___x_451_, v___x_452_);
v___x_454_ = lean_uint64_add(v___x_447_, v___x_453_);
v___x_455_ = lean_box_uint64(v___x_454_);
v___x_456_ = lean_array_push(v_b_395_, v___x_455_);
v___x_457_ = lean_nat_add(v_i_396_, v_step_399_);
lean_dec(v_i_396_);
v_b_395_ = v___x_456_;
v_i_396_ = v___x_457_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___boxed(mut v_a_459_: *mut lean_object, mut v_range_460_: *mut lean_object, mut v_b_461_: *mut lean_object, mut v_i_462_: *mut lean_object, mut v___y_463_: *mut lean_object) -> *mut lean_object{
let mut v_res_464_: *mut lean_object = core::ptr::null_mut(); 
v_res_464_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(v_a_459_, v_range_460_, v_b_461_, v_i_462_);
lean_dec_ref(v_range_460_);
lean_dec_ref(v_a_459_);
return v_res_464_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__2(mut v_snd_465_: *mut lean_object, mut v___x_466_: *mut lean_object, mut v_arr_467_: *mut lean_object, mut v___x_468_: *mut lean_object) -> *mut lean_object{
let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); let mut v_a_471_: *mut lean_object = core::ptr::null_mut(); let mut v___x_472_: *mut lean_object = core::ptr::null_mut(); let mut v_a_473_: *mut lean_object = core::ptr::null_mut(); let mut v___x_475_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_476_: u8 = 0; let mut v___x_478_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_479_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_480_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_470_ = l_IO_FS_readBinFile(v_snd_465_);
if lean_obj_tag(v___x_470_) == 0 {
let mut v_a_471_: *mut lean_object = core::ptr::null_mut(); let mut v___x_472_: *mut lean_object = core::ptr::null_mut(); 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(v_a_471_, v___x_466_, v_arr_467_, v___x_468_);
lean_dec(v_a_471_);
return v___x_472_;
} else {
let mut v_a_473_: *mut lean_object = core::ptr::null_mut(); let mut v___x_475_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_476_: u8 = 0; let mut v_isSharedCheck_480_: u8 = 0; 
lean_dec(v___x_468_);
lean_dec_ref(v_arr_467_);
v_a_473_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_480_ = (!lean_is_exclusive(v___x_470_)) as u8;
if v_isSharedCheck_480_ == 0 {
v___x_475_ = v___x_470_;
v_isShared_476_ = v_isSharedCheck_480_;
state = 1; continue;
} else {
lean_inc(v_a_473_);
lean_dec(v___x_470_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
state = 1; continue;
}
}
}
1 => {
if v_isShared_476_ == 0 {
v___x_478_ = v___x_475_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_479_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__2___boxed(mut v_snd_481_: *mut lean_object, mut v___x_482_: *mut lean_object, mut v_arr_483_: *mut lean_object, mut v___x_484_: *mut lean_object, mut v___y_485_: *mut lean_object) -> *mut lean_object{
let mut v_res_486_: *mut lean_object = core::ptr::null_mut(); 
v_res_486_ = l_main___lam__2(v_snd_481_, v___x_482_, v_arr_483_, v___x_484_);
lean_dec_ref(v___x_482_);
lean_dec_ref(v_snd_481_);
return v_res_486_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__5___redArg(mut v_range_487_: *mut lean_object, mut v_b_488_: *mut lean_object, mut v_i_489_: *mut lean_object) -> *mut lean_object{
let mut v_stop_491_: *mut lean_object = core::ptr::null_mut(); let mut v_step_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_493_: u8 = 0; let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_495_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_499_: u8 = 0; let mut v___x_500_: *mut lean_object = core::ptr::null_mut(); let mut v___x_501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: u64 = 0; let mut v___x_504_: u64 = 0; let mut v___x_505_: u64 = 0; let mut v___x_506_: u64 = 0; let mut v_x_507_: u64 = 0; let mut v___x_508_: u64 = 0; let mut v___x_509_: u64 = 0; let mut v_x_510_: u64 = 0; let mut v___x_511_: u64 = 0; let mut v___x_512_: u64 = 0; let mut v_x_513_: u64 = 0; let mut v___x_514_: u64 = 0; let mut v___x_515_: u64 = 0; let mut v___x_516_: *mut lean_object = core::ptr::null_mut(); let mut v___x_517_: u64 = 0; let mut v___x_518_: u64 = 0; let mut v___x_519_: *mut lean_object = core::ptr::null_mut(); let mut v___x_520_: *mut lean_object = core::ptr::null_mut(); let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); let mut v___x_524_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_526_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_527_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_stop_491_ = lean_ctor_get(v_range_487_, 1);
v_step_492_ = lean_ctor_get(v_range_487_, 2);
v___x_493_ = lean_nat_dec_lt(v_i_489_, v_stop_491_);
if v___x_493_ == 0 {
let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_489_);
v___x_494_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_494_, 0, v_b_488_);
return v___x_494_;
} else {
let mut v_fst_495_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_499_: u8 = 0; let mut v_isSharedCheck_527_: u8 = 0; 
v_fst_495_ = lean_ctor_get(v_b_488_, 0);
v_snd_496_ = lean_ctor_get(v_b_488_, 1);
v_isSharedCheck_527_ = (!lean_is_exclusive(v_b_488_)) as u8;
if v_isSharedCheck_527_ == 0 {
v___x_498_ = v_b_488_;
v_isShared_499_ = v_isSharedCheck_527_;
state = 1; continue;
} else {
lean_inc(v_snd_496_);
lean_inc(v_fst_495_);
lean_dec(v_b_488_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_527_;
state = 1; continue;
}
}
}
1 => {
v___x_500_ = lean_unsigned_to_nat(6249999);
v___x_501_ = lean_unsigned_to_nat(1);
v___x_502_ = lean_nat_sub(v___x_500_, v_i_489_);
v___x_503_ = 12u64;
v___x_504_ = lean_unbox_uint64(v_snd_496_);
v___x_505_ = lean_uint64_shift_right(v___x_504_, v___x_503_);
v___x_506_ = lean_unbox_uint64(v_snd_496_);
lean_dec(v_snd_496_);
v_x_507_ = lean_uint64_xor(v___x_506_, v___x_505_);
v___x_508_ = 25u64;
v___x_509_ = lean_uint64_shift_left(v_x_507_, v___x_508_);
v_x_510_ = lean_uint64_xor(v_x_507_, v___x_509_);
v___x_511_ = 27u64;
v___x_512_ = lean_uint64_shift_right(v_x_510_, v___x_511_);
v_x_513_ = lean_uint64_xor(v_x_510_, v___x_512_);
v___x_514_ = 2685821657736338717u64;
v___x_515_ = lean_uint64_mul(v_x_513_, v___x_514_);
v___x_516_ = lean_nat_add(v___x_502_, v___x_501_);
v___x_517_ = lean_uint64_of_nat(v___x_516_);
lean_dec(v___x_516_);
v___x_518_ = lean_uint64_mod(v___x_515_, v___x_517_);
v___x_519_ = lean_uint64_to_nat(v___x_518_);
v___x_520_ = lean_array_swap(v_fst_495_, v___x_502_, v___x_519_);
lean_dec(v___x_519_);
lean_dec(v___x_502_);
v___x_521_ = lean_box_uint64(v_x_513_);
if v_isShared_499_ == 0 {
lean_ctor_set(v___x_498_, 1, v___x_521_);
lean_ctor_set(v___x_498_, 0, v___x_520_);
v___x_523_ = v___x_498_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_526_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_526_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__5___redArg___boxed(mut v_range_528_: *mut lean_object, mut v_b_529_: *mut lean_object, mut v_i_530_: *mut lean_object, mut v___y_531_: *mut lean_object) -> *mut lean_object{
let mut v_res_532_: *mut lean_object = core::ptr::null_mut(); 
v_res_532_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__5___redArg(v_range_528_, v_b_529_, v_i_530_);
lean_dec_ref(v_range_528_);
return v_res_532_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__3(mut v___x_533_: *mut lean_object, mut v___x_534_: *mut lean_object, mut v___x_535_: *mut lean_object) -> *mut lean_object{
let mut v___x_537_: *mut lean_object = core::ptr::null_mut(); let mut v_a_538_: *mut lean_object = core::ptr::null_mut(); let mut v___x_540_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_541_: u8 = 0; let mut v_fst_542_: *mut lean_object = core::ptr::null_mut(); let mut v___x_544_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_545_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_546_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_537_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__5___redArg(v___x_533_, v___x_534_, v___x_535_);
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_546_ = (!lean_is_exclusive(v___x_537_)) as u8;
if v_isSharedCheck_546_ == 0 {
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_546_;
state = 1; continue;
} else {
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
state = 1; continue;
}
}
1 => {
v_fst_542_ = lean_ctor_get(v_a_538_, 0);
lean_inc(v_fst_542_);
lean_dec(v_a_538_);
if v_isShared_541_ == 0 {
lean_ctor_set(v___x_540_, 0, v_fst_542_);
v___x_544_ = v___x_540_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_545_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_fst_542_);
v___x_544_ = v_reuseFailAlloc_545_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__3___boxed(mut v___x_547_: *mut lean_object, mut v___x_548_: *mut lean_object, mut v___x_549_: *mut lean_object, mut v___y_550_: *mut lean_object) -> *mut lean_object{
let mut v_res_551_: *mut lean_object = core::ptr::null_mut(); 
v_res_551_ = l_main___lam__3(v___x_547_, v___x_548_, v___x_549_);
lean_dec_ref(v___x_547_);
return v_res_551_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__2_spec__3(mut v_s_552_: *mut lean_object) -> *mut lean_object{
let mut v___x_554_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_555_: *mut lean_object = core::ptr::null_mut(); let mut v___x_556_: *mut lean_object = core::ptr::null_mut(); 
v___x_554_ = lean_get_stdout();
v_putStr_555_ = lean_ctor_get(v___x_554_, 4);
lean_inc_ref(v_putStr_555_);
lean_dec_ref(v___x_554_);
v___x_556_ = lean_apply_2(v_putStr_555_, v_s_552_, lean_box(0));
return v___x_556_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__2_spec__3___boxed(mut v_s_557_: *mut lean_object, mut v_a_558_: *mut lean_object) -> *mut lean_object{
let mut v_res_559_: *mut lean_object = core::ptr::null_mut(); 
v_res_559_ = l_IO_print___at___00IO_println___at___00main_spec__2_spec__3(v_s_557_);
return v_res_559_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2(mut v_s_560_: *mut lean_object) -> *mut lean_object{
let mut v___x_562_: u32 = 0; let mut v___x_563_: *mut lean_object = core::ptr::null_mut(); let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); 
v___x_562_ = 10;
v___x_563_ = lean_string_push(v_s_560_, v___x_562_);
v___x_564_ = l_IO_print___at___00IO_println___at___00main_spec__2_spec__3(v___x_563_);
return v___x_564_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2___boxed(mut v_s_565_: *mut lean_object, mut v_a_566_: *mut lean_object) -> *mut lean_object{
let mut v_res_567_: *mut lean_object = core::ptr::null_mut(); 
v_res_567_ = l_IO_println___at___00main_spec__2(v_s_565_);
return v_res_567_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_574_: *mut lean_object = core::ptr::null_mut(); let mut v_arr_575_: *mut lean_object = core::ptr::null_mut(); let mut v___x_576_: *mut lean_object = core::ptr::null_mut(); let mut v___x_577_: *mut lean_object = core::ptr::null_mut(); 
v___x_574_ = lean_unsigned_to_nat(6250000);
v_arr_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
v___x_576_ = l_main___closed__1___boxed__const__1;
v___x_577_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_arr_575_);
return v___x_577_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_578_: *mut lean_object = core::ptr::null_mut(); let mut v___x_579_: *mut lean_object = core::ptr::null_mut(); let mut v___x_580_: *mut lean_object = core::ptr::null_mut(); let mut v___f_581_: *mut lean_object = core::ptr::null_mut(); 
v___x_578_ = lean_unsigned_to_nat(0);
v___x_579_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_580_ = l_main___closed__0;
v___f_581_ = lean_alloc_closure(l_main___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_581_, 0, v___x_580_);
lean_closure_set(v___f_581_, 1, v___x_579_);
lean_closure_set(v___f_581_, 2, v___x_578_);
return v___f_581_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_584_: *mut lean_object = core::ptr::null_mut(); let mut v___x_585_: *mut lean_object = core::ptr::null_mut(); 
v___x_584_ = lean_unsigned_to_nat(50000000);
v___x_585_ = lean_mk_empty_byte_array(v___x_584_);
return v___x_585_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_594_: *mut lean_object = core::ptr::null_mut(); let mut v_arr_595_: *mut lean_object = core::ptr::null_mut(); let mut v___x_596_: *mut lean_object = core::ptr::null_mut(); let mut v___x_597_: *mut lean_object = core::ptr::null_mut(); let mut v___x_598_: *mut lean_object = core::ptr::null_mut(); let mut v___f_599_: *mut lean_object = core::ptr::null_mut(); let mut v___x_600_: *mut lean_object = core::ptr::null_mut(); let mut v_a_601_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_602_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_603_: *mut lean_object = core::ptr::null_mut(); let mut v___x_604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_605_: f64 = 0.0; let mut v___x_606_: *mut lean_object = core::ptr::null_mut(); let mut v___x_607_: *mut lean_object = core::ptr::null_mut(); let mut v___x_608_: *mut lean_object = core::ptr::null_mut(); let mut v___x_609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_610_: *mut lean_object = core::ptr::null_mut(); let mut v___x_611_: *mut lean_object = core::ptr::null_mut(); let mut v_a_612_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_613_: *mut lean_object = core::ptr::null_mut(); let mut v___x_614_: *mut lean_object = core::ptr::null_mut(); let mut v___x_615_: *mut lean_object = core::ptr::null_mut(); let mut v___x_616_: *mut lean_object = core::ptr::null_mut(); let mut v___f_617_: *mut lean_object = core::ptr::null_mut(); let mut v___x_618_: *mut lean_object = core::ptr::null_mut(); let mut v_a_619_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_620_: *mut lean_object = core::ptr::null_mut(); let mut v___x_621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_622_: f64 = 0.0; let mut v___x_623_: *mut lean_object = core::ptr::null_mut(); let mut v___x_624_: *mut lean_object = core::ptr::null_mut(); let mut v___x_625_: *mut lean_object = core::ptr::null_mut(); let mut v___x_626_: *mut lean_object = core::ptr::null_mut(); let mut v___f_627_: *mut lean_object = core::ptr::null_mut(); let mut v___x_628_: *mut lean_object = core::ptr::null_mut(); let mut v_a_629_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_630_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_631_: *mut lean_object = core::ptr::null_mut(); let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_634_: u8 = 0; let mut v___x_635_: *mut lean_object = core::ptr::null_mut(); let mut v___x_636_: f64 = 0.0; let mut v___x_637_: *mut lean_object = core::ptr::null_mut(); let mut v___x_638_: *mut lean_object = core::ptr::null_mut(); let mut v___x_639_: *mut lean_object = core::ptr::null_mut(); let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); let mut v___x_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_642_: *mut lean_object = core::ptr::null_mut(); let mut v___x_644_: *mut lean_object = core::ptr::null_mut(); let mut v___f_645_: *mut lean_object = core::ptr::null_mut(); let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v_a_647_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_648_: *mut lean_object = core::ptr::null_mut(); let mut v___x_649_: *mut lean_object = core::ptr::null_mut(); let mut v___x_650_: f64 = 0.0; let mut v___x_651_: *mut lean_object = core::ptr::null_mut(); let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v_a_655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_657_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_658_: u8 = 0; let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_661_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_662_: u8 = 0; let mut v_reuseFailAlloc_663_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_664_: u8 = 0; let mut v_a_665_: *mut lean_object = core::ptr::null_mut(); let mut v___x_667_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_668_: u8 = 0; let mut v___x_670_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_671_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_672_: u8 = 0; let mut v_a_673_: *mut lean_object = core::ptr::null_mut(); let mut v___x_675_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_676_: u8 = 0; let mut v___x_678_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_679_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_680_: u8 = 0; let mut v_a_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_684_: u8 = 0; let mut v___x_686_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_687_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_688_: u8 = 0; let mut v_a_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_692_: u8 = 0; let mut v___x_694_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_695_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_696_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_594_ = lean_unsigned_to_nat(6250000);
v_arr_595_ = lean_mk_empty_array_with_capacity(v___x_594_);
v___x_596_ = lean_unsigned_to_nat(0);
v___x_597_ = lean_unsigned_to_nat(1);
v___x_598_ = l_main___closed__0;
v___f_599_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_600_ = l_timeS___redArg(v___f_599_);
if lean_obj_tag(v___x_600_) == 0 {
let mut v_a_601_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_602_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_603_: *mut lean_object = core::ptr::null_mut(); let mut v___x_604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_605_: f64 = 0.0; let mut v___x_606_: *mut lean_object = core::ptr::null_mut(); let mut v___x_607_: *mut lean_object = core::ptr::null_mut(); let mut v___x_608_: *mut lean_object = core::ptr::null_mut(); let mut v___x_609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_610_: *mut lean_object = core::ptr::null_mut(); 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v_fst_602_ = lean_ctor_get(v_a_601_, 0);
lean_inc(v_fst_602_);
v_snd_603_ = lean_ctor_get(v_a_601_, 1);
lean_inc(v_snd_603_);
lean_dec(v_a_601_);
v___x_604_ = l_main___closed__3;
v___x_605_ = lean_unbox_float(v_snd_603_);
lean_dec(v_snd_603_);
v___x_606_ = lean_float_to_string(v___x_605_);
v___x_607_ = lean_string_append(v___x_604_, v___x_606_);
lean_dec_ref(v___x_606_);
v___x_608_ = l_main___closed__4;
v___x_609_ = lean_string_append(v___x_607_, v___x_608_);
v___x_610_ = l_IO_println___at___00main_spec__2(v___x_609_);
if lean_obj_tag(v___x_610_) == 0 {
let mut v___x_611_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_610_, 1);
v___x_611_ = lean_io_create_tempfile();
if lean_obj_tag(v___x_611_) == 0 {
let mut v_a_612_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_613_: *mut lean_object = core::ptr::null_mut(); let mut v___x_614_: *mut lean_object = core::ptr::null_mut(); let mut v___x_615_: *mut lean_object = core::ptr::null_mut(); let mut v___x_616_: *mut lean_object = core::ptr::null_mut(); let mut v___f_617_: *mut lean_object = core::ptr::null_mut(); let mut v___x_618_: *mut lean_object = core::ptr::null_mut(); 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
v_snd_613_ = lean_ctor_get(v_a_612_, 1);
lean_inc_n(v_snd_613_, 2);
lean_dec(v_a_612_);
v___x_614_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_615_ = lean_array_get_size(v_fst_602_);
v___x_616_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_616_, 0, v___x_596_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
lean_ctor_set(v___x_616_, 2, v___x_597_);
v___f_617_ = lean_alloc_closure(l_main___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
lean_closure_set(v___f_617_, 0, v_fst_602_);
lean_closure_set(v___f_617_, 1, v___x_616_);
lean_closure_set(v___f_617_, 2, v___x_614_);
lean_closure_set(v___f_617_, 3, v___x_596_);
lean_closure_set(v___f_617_, 4, v_snd_613_);
v___x_618_ = l_timeS___redArg(v___f_617_);
if lean_obj_tag(v___x_618_) == 0 {
let mut v_a_619_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_620_: *mut lean_object = core::ptr::null_mut(); let mut v___x_621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_622_: f64 = 0.0; let mut v___x_623_: *mut lean_object = core::ptr::null_mut(); let mut v___x_624_: *mut lean_object = core::ptr::null_mut(); let mut v___x_625_: *mut lean_object = core::ptr::null_mut(); let mut v___x_626_: *mut lean_object = core::ptr::null_mut(); 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v_snd_620_ = lean_ctor_get(v_a_619_, 1);
lean_inc(v_snd_620_);
lean_dec(v_a_619_);
v___x_621_ = l_main___closed__6;
v___x_622_ = lean_unbox_float(v_snd_620_);
lean_dec(v_snd_620_);
v___x_623_ = lean_float_to_string(v___x_622_);
v___x_624_ = lean_string_append(v___x_621_, v___x_623_);
lean_dec_ref(v___x_623_);
v___x_625_ = lean_string_append(v___x_624_, v___x_608_);
v___x_626_ = l_IO_println___at___00main_spec__2(v___x_625_);
if lean_obj_tag(v___x_626_) == 0 {
let mut v___f_627_: *mut lean_object = core::ptr::null_mut(); let mut v___x_628_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_626_, 1);
v___f_627_ = lean_alloc_closure(l_main___lam__2___boxed as *mut core::ffi::c_void, 5, 4);
lean_closure_set(v___f_627_, 0, v_snd_613_);
lean_closure_set(v___f_627_, 1, v___x_598_);
lean_closure_set(v___f_627_, 2, v_arr_595_);
lean_closure_set(v___f_627_, 3, v___x_596_);
v___x_628_ = l_timeS___redArg(v___f_627_);
if lean_obj_tag(v___x_628_) == 0 {
let mut v_a_629_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_630_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_631_: *mut lean_object = core::ptr::null_mut(); let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_634_: u8 = 0; let mut v_isSharedCheck_664_: u8 = 0; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v_fst_630_ = lean_ctor_get(v_a_629_, 0);
v_snd_631_ = lean_ctor_get(v_a_629_, 1);
v_isSharedCheck_664_ = (!lean_is_exclusive(v_a_629_)) as u8;
if v_isSharedCheck_664_ == 0 {
v___x_633_ = v_a_629_;
v_isShared_634_ = v_isSharedCheck_664_;
state = 1; continue;
} else {
lean_inc(v_snd_631_);
lean_inc(v_fst_630_);
lean_dec(v_a_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_664_;
state = 1; continue;
}
} else {
let mut v_a_665_: *mut lean_object = core::ptr::null_mut(); let mut v___x_667_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_668_: u8 = 0; let mut v_isSharedCheck_672_: u8 = 0; 
v_a_665_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_672_ = (!lean_is_exclusive(v___x_628_)) as u8;
if v_isSharedCheck_672_ == 0 {
v___x_667_ = v___x_628_;
v_isShared_668_ = v_isSharedCheck_672_;
state = 5; continue;
} else {
lean_inc(v_a_665_);
lean_dec(v___x_628_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
state = 5; continue;
}
}
} else {
lean_dec(v_snd_613_);
lean_dec_ref(v_arr_595_);
return v___x_626_;
}
} else {
let mut v_a_673_: *mut lean_object = core::ptr::null_mut(); let mut v___x_675_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_676_: u8 = 0; let mut v_isSharedCheck_680_: u8 = 0; 
lean_dec(v_snd_613_);
lean_dec_ref(v_arr_595_);
v_a_673_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_680_ = (!lean_is_exclusive(v___x_618_)) as u8;
if v_isSharedCheck_680_ == 0 {
v___x_675_ = v___x_618_;
v_isShared_676_ = v_isSharedCheck_680_;
state = 7; continue;
} else {
lean_inc(v_a_673_);
lean_dec(v___x_618_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
state = 7; continue;
}
}
} else {
let mut v_a_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_684_: u8 = 0; let mut v_isSharedCheck_688_: u8 = 0; 
lean_dec(v_fst_602_);
lean_dec_ref(v_arr_595_);
v_a_681_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_688_ = (!lean_is_exclusive(v___x_611_)) as u8;
if v_isSharedCheck_688_ == 0 {
v___x_683_ = v___x_611_;
v_isShared_684_ = v_isSharedCheck_688_;
state = 9; continue;
} else {
lean_inc(v_a_681_);
lean_dec(v___x_611_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
state = 9; continue;
}
}
} else {
lean_dec(v_fst_602_);
lean_dec_ref(v_arr_595_);
return v___x_610_;
}
} else {
let mut v_a_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_692_: u8 = 0; let mut v_isSharedCheck_696_: u8 = 0; 
lean_dec_ref(v_arr_595_);
v_a_689_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_696_ = (!lean_is_exclusive(v___x_600_)) as u8;
if v_isSharedCheck_696_ == 0 {
v___x_691_ = v___x_600_;
v_isShared_692_ = v_isSharedCheck_696_;
state = 11; continue;
} else {
lean_inc(v_a_689_);
lean_dec(v___x_600_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
state = 11; continue;
}
}
}
1 => {
v___x_635_ = l_main___closed__7;
v___x_636_ = lean_unbox_float(v_snd_631_);
lean_dec(v_snd_631_);
v___x_637_ = lean_float_to_string(v___x_636_);
v___x_638_ = lean_string_append(v___x_635_, v___x_637_);
lean_dec_ref(v___x_637_);
v___x_639_ = lean_string_append(v___x_638_, v___x_608_);
v___x_640_ = l_IO_println___at___00main_spec__2(v___x_639_);
if lean_obj_tag(v___x_640_) == 0 {
let mut v___x_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_642_: *mut lean_object = core::ptr::null_mut(); let mut v___x_644_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_640_, 1);
v___x_641_ = l_main___closed__8;
v___x_642_ = l_main___closed__1___boxed__const__1;
if v_isShared_634_ == 0 {
lean_ctor_set(v___x_633_, 1, v___x_642_);
v___x_644_ = v___x_633_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_663_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_fst_630_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_663_;
state = 2; continue;
}
} else {
lean_del_object(v___x_633_);
lean_dec(v_fst_630_);
return v___x_640_;
}
}
5 => {
if v_isShared_668_ == 0 {
v___x_670_ = v___x_667_;
state = 6; continue;
} else {
let mut v_reuseFailAlloc_671_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
state = 6; continue;
}
}
7 => {
if v_isShared_676_ == 0 {
v___x_678_ = v___x_675_;
state = 8; continue;
} else {
let mut v_reuseFailAlloc_679_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
state = 8; continue;
}
}
9 => {
if v_isShared_684_ == 0 {
v___x_686_ = v___x_683_;
state = 10; continue;
} else {
let mut v_reuseFailAlloc_687_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
state = 10; continue;
}
}
11 => {
if v_isShared_692_ == 0 {
v___x_694_ = v___x_691_;
state = 12; continue;
} else {
let mut v_reuseFailAlloc_695_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
state = 12; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_697_: *mut lean_object) -> *mut lean_object{
let mut v_res_698_: *mut lean_object = core::ptr::null_mut(); 
v_res_698_ = _lean_main();
return v_res_698_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__0(mut v_range_699_: *mut lean_object, mut v_b_700_: *mut lean_object, mut v_i_701_: *mut lean_object, mut v_hs_702_: *mut lean_object, mut v_hl_703_: *mut lean_object) -> *mut lean_object{
let mut v___x_705_: *mut lean_object = core::ptr::null_mut(); 
v___x_705_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__0___redArg(v_range_699_, v_b_700_, v_i_701_);
return v___x_705_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__0___boxed(mut v_range_706_: *mut lean_object, mut v_b_707_: *mut lean_object, mut v_i_708_: *mut lean_object, mut v_hs_709_: *mut lean_object, mut v_hl_710_: *mut lean_object, mut v___y_711_: *mut lean_object) -> *mut lean_object{
let mut v_res_712_: *mut lean_object = core::ptr::null_mut(); 
v_res_712_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__0(v_range_706_, v_b_707_, v_i_708_, v_hs_709_, v_hl_710_);
lean_dec_ref(v_range_706_);
return v_res_712_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3(mut v_fst_713_: *mut lean_object, mut v_range_714_: *mut lean_object, mut v_b_715_: *mut lean_object, mut v_i_716_: *mut lean_object, mut v_hs_717_: *mut lean_object, mut v_hl_718_: *mut lean_object) -> *mut lean_object{
let mut v___x_720_: *mut lean_object = core::ptr::null_mut(); 
v___x_720_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(v_fst_713_, v_range_714_, v_b_715_, v_i_716_);
return v___x_720_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___boxed(mut v_fst_721_: *mut lean_object, mut v_range_722_: *mut lean_object, mut v_b_723_: *mut lean_object, mut v_i_724_: *mut lean_object, mut v_hs_725_: *mut lean_object, mut v_hl_726_: *mut lean_object, mut v___y_727_: *mut lean_object) -> *mut lean_object{
let mut v_res_728_: *mut lean_object = core::ptr::null_mut(); 
v_res_728_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3(v_fst_721_, v_range_722_, v_b_723_, v_i_724_, v_hs_725_, v_hl_726_);
lean_dec_ref(v_range_722_);
lean_dec_ref(v_fst_721_);
return v_res_728_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4(mut v_a_729_: *mut lean_object, mut v_range_730_: *mut lean_object, mut v_b_731_: *mut lean_object, mut v_i_732_: *mut lean_object, mut v_hs_733_: *mut lean_object, mut v_hl_734_: *mut lean_object) -> *mut lean_object{
let mut v___x_736_: *mut lean_object = core::ptr::null_mut(); 
v___x_736_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(v_a_729_, v_range_730_, v_b_731_, v_i_732_);
return v___x_736_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___boxed(mut v_a_737_: *mut lean_object, mut v_range_738_: *mut lean_object, mut v_b_739_: *mut lean_object, mut v_i_740_: *mut lean_object, mut v_hs_741_: *mut lean_object, mut v_hl_742_: *mut lean_object, mut v___y_743_: *mut lean_object) -> *mut lean_object{
let mut v_res_744_: *mut lean_object = core::ptr::null_mut(); 
v_res_744_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4(v_a_737_, v_range_738_, v_b_739_, v_i_740_, v_hs_741_, v_hl_742_);
lean_dec_ref(v_range_738_);
lean_dec_ref(v_a_737_);
return v_res_744_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__5(mut v_range_745_: *mut lean_object, mut v_b_746_: *mut lean_object, mut v_i_747_: *mut lean_object, mut v_hs_748_: *mut lean_object, mut v_hl_749_: *mut lean_object) -> *mut lean_object{
let mut v___x_751_: *mut lean_object = core::ptr::null_mut(); 
v___x_751_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__5___redArg(v_range_745_, v_b_746_, v_i_747_);
return v___x_751_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__5___boxed(mut v_range_752_: *mut lean_object, mut v_b_753_: *mut lean_object, mut v_i_754_: *mut lean_object, mut v_hs_755_: *mut lean_object, mut v_hl_756_: *mut lean_object, mut v___y_757_: *mut lean_object) -> *mut lean_object{
let mut v_res_758_: *mut lean_object = core::ptr::null_mut(); 
v_res_758_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__5(v_range_752_, v_b_753_, v_i_754_, v_hs_755_, v_hl_756_);
lean_dec_ref(v_range_752_);
return v_res_758_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1(mut v_n_759_: *mut lean_object, mut v_as_760_: *mut lean_object, mut v_lo_761_: *mut lean_object, mut v_hi_762_: *mut lean_object, mut v_w_763_: *mut lean_object, mut v_hlo_764_: *mut lean_object, mut v_hhi_765_: *mut lean_object) -> *mut lean_object{
let mut v___x_766_: *mut lean_object = core::ptr::null_mut(); 
v___x_766_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1___redArg(v_n_759_, v_as_760_, v_lo_761_, v_hi_762_);
return v___x_766_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1___boxed(mut v_n_767_: *mut lean_object, mut v_as_768_: *mut lean_object, mut v_lo_769_: *mut lean_object, mut v_hi_770_: *mut lean_object, mut v_w_771_: *mut lean_object, mut v_hlo_772_: *mut lean_object, mut v_hhi_773_: *mut lean_object) -> *mut lean_object{
let mut v_res_774_: *mut lean_object = core::ptr::null_mut(); 
v_res_774_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1(v_n_767_, v_as_768_, v_lo_769_, v_hi_770_, v_w_771_, v_hlo_772_, v_hhi_773_);
lean_dec(v_hi_770_);
lean_dec(v_n_767_);
return v_res_774_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1_spec__2(mut v_n_775_: *mut lean_object, mut v_lo_776_: *mut lean_object, mut v_hi_777_: *mut lean_object, mut v_hhi_778_: *mut lean_object, mut v_pivot_779_: u64, mut v_as_780_: *mut lean_object, mut v_i_781_: *mut lean_object, mut v_k_782_: *mut lean_object, mut v_ilo_783_: *mut lean_object, mut v_ik_784_: *mut lean_object, mut v_w_785_: *mut lean_object) -> *mut lean_object{
let mut v___x_786_: *mut lean_object = core::ptr::null_mut(); 
v___x_786_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1_spec__2___redArg(v_hi_777_, v_pivot_779_, v_as_780_, v_i_781_, v_k_782_);
return v___x_786_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1_spec__2___boxed(mut v_n_787_: *mut lean_object, mut v_lo_788_: *mut lean_object, mut v_hi_789_: *mut lean_object, mut v_hhi_790_: *mut lean_object, mut v_pivot_791_: *mut lean_object, mut v_as_792_: *mut lean_object, mut v_i_793_: *mut lean_object, mut v_k_794_: *mut lean_object, mut v_ilo_795_: *mut lean_object, mut v_ik_796_: *mut lean_object, mut v_w_797_: *mut lean_object) -> *mut lean_object{
let mut v_pivot_boxed_798_: u64 = 0; let mut v_res_799_: *mut lean_object = core::ptr::null_mut(); 
v_pivot_boxed_798_ = lean_unbox_uint64(v_pivot_791_);
lean_dec_ref(v_pivot_791_);
v_res_799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00main_spec__1_spec__1_spec__2(v_n_787_, v_lo_788_, v_hi_789_, v_hhi_790_, v_pivot_boxed_798_, v_as_792_, v_i_793_, v_k_794_, v_ilo_795_, v_ik_796_, v_w_797_);
lean_dec(v_hi_789_);
lean_dec(v_lo_788_);
lean_dec(v_n_787_);
return v_res_799_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_io__compute(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_N = _init_l_N();
lean_mark_persistent(l_N);
l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed__const__1 = _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed__const__1();
lean_mark_persistent(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_io__compute(1 /* builtin */);
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
