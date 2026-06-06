// Lean compiler output
// Module: initUnboxed
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_float_to_string(_: f64) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn l_Float_ofScientific(_: *mut lean_object, _: u8, _: *mut lean_object) -> f64;
    fn lean_uint64_to_nat(_: u64) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_usize_to_nat(_: usize) -> *mut lean_object;
    fn lean_uint32_to_nat(_: u32) -> *mut lean_object;
}
#[no_mangle] pub static l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2887224489____hygCtx___hyg_2__value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*0 + 8) as u16, m_other: 0, m_tag: 0 }, m_objs: [0 as *mut lean_object] };
#[no_mangle] pub static mut l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2887224489____hygCtx___hyg_2_: *mut lean_object = core::ptr::addr_of!(l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2887224489____hygCtx___hyg_2__value) as *mut lean_object;
#[no_mangle] pub static mut l_test: u64 = 0;
#[no_mangle] pub static mut l_testb: u8 = 0;
#[no_mangle] pub static l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2016441482____hygCtx___hyg_2__value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + core::mem::size_of::<usize>()*1) as u16, m_other: 1, m_tag: 0 }, m_objs: [(1 as *mut lean_object)] };
#[no_mangle] pub static mut l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2016441482____hygCtx___hyg_2_: *mut lean_object = core::ptr::addr_of!(l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2016441482____hygCtx___hyg_2__value) as *mut lean_object;
#[no_mangle] pub static mut l_testu: usize = 0;
static mut l___private_initUnboxed_0__initFn___closed__0_00___x40_initUnboxed_744502646____hygCtx___hyg_2__once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___private_initUnboxed_0__initFn___closed__0_00___x40_initUnboxed_744502646____hygCtx___hyg_2_: f64 = 0.0;
#[no_mangle] pub static mut l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_744502646____hygCtx___hyg_2_: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_testf: f64 = 0.0;
#[no_mangle] pub static mut l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_test32: u32 = 0;
#[no_mangle] pub static l_IO_println___at___00main_spec__1___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_IO_println___at___00main_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_IO_println___at___00main_spec__1___closed__1_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_IO_println___at___00main_spec__1___closed__1: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__1_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2887224489____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2887224489____hygCtx___hyg_2_;
v___x_5_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2887224489____hygCtx___hyg_2____boxed(mut v_a_6_: *mut lean_object) -> *mut lean_object{
let mut v_res_7_: *mut lean_object = core::ptr::null_mut(); 
v_res_7_ = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2887224489____hygCtx___hyg_2_();
return v_res_7_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_3445265930____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_9_: u8 = 0; let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); 
v___x_9_ = 0;
v___x_10_ = lean_box((v___x_9_) as usize);
v___x_11_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_3445265930____hygCtx___hyg_2____boxed(mut v_a_12_: *mut lean_object) -> *mut lean_object{
let mut v_res_13_: *mut lean_object = core::ptr::null_mut(); 
v_res_13_ = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_3445265930____hygCtx___hyg_2_();
return v_res_13_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2016441482____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); 
v___x_17_ = l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2016441482____hygCtx___hyg_2_;
v___x_18_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2016441482____hygCtx___hyg_2____boxed(mut v_a_19_: *mut lean_object) -> *mut lean_object{
let mut v_res_20_: *mut lean_object = core::ptr::null_mut(); 
v_res_20_ = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2016441482____hygCtx___hyg_2_();
return v_res_20_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___private_initUnboxed_0__initFn___closed__0_00___x40_initUnboxed_744502646____hygCtx___hyg_2_() -> f64{
let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: u8 = 0; let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: f64 = 0.0; 
v___x_21_ = lean_unsigned_to_nat(1);
v___x_22_ = 1;
v___x_23_ = lean_unsigned_to_nat(5);
v___x_24_ = l_Float_ofScientific(v___x_23_, v___x_22_, v___x_21_);
return v___x_24_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_744502646____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_25_: f64 = 0.0; let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
v___x_25_ = lean_float_once(core::ptr::addr_of_mut!(l___private_initUnboxed_0__initFn___closed__0_00___x40_initUnboxed_744502646____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_initUnboxed_0__initFn___closed__0_00___x40_initUnboxed_744502646____hygCtx___hyg_2__once), _init_l___private_initUnboxed_0__initFn___closed__0_00___x40_initUnboxed_744502646____hygCtx___hyg_2_);
v___x_26_ = lean_box_float(v___x_25_);
return v___x_26_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_744502646____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); 
v___x_28_ = l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_744502646____hygCtx___hyg_2_;
v___x_29_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_744502646____hygCtx___hyg_2____boxed(mut v_a_30_: *mut lean_object) -> *mut lean_object{
let mut v_res_31_: *mut lean_object = core::ptr::null_mut(); 
v_res_31_ = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_744502646____hygCtx___hyg_2_();
return v_res_31_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_32_: u32 = 0; let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); 
v___x_32_ = 16;
v___x_33_ = lean_box_uint32(v___x_32_);
return v___x_33_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); 
v___x_35_ = l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_;
v___x_36_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2208129052____hygCtx___hyg_2____boxed(mut v_a_37_: *mut lean_object) -> *mut lean_object{
let mut v_res_38_: *mut lean_object = core::ptr::null_mut(); 
v_res_38_ = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_();
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
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__4(mut v_s_47_: u32) -> *mut lean_object{
let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: u32 = 0; let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); 
v___x_49_ = lean_uint32_to_nat(v_s_47_);
v___x_50_ = l_Nat_reprFast(v___x_49_);
v___x_51_ = 10;
v___x_52_ = lean_string_push(v___x_50_, v___x_51_);
v___x_53_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_52_);
return v___x_53_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__4___boxed(mut v_s_54_: *mut lean_object, mut v_a_55_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_56_: u32 = 0; let mut v_res_57_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_56_ = lean_unbox_uint32(v_s_54_);
lean_dec(v_s_54_);
v_res_57_ = l_IO_println___at___00main_spec__4(v_s_boxed_56_);
return v_res_57_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_60_: u8) -> *mut lean_object{
let mut v___y_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: u32 = 0; let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if v_s_60_ == 0 {
let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v___x_67_ = l_IO_println___at___00main_spec__1___closed__0;
v___y_63_ = v___x_67_;
state = 1; continue;
} else {
let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); 
v___x_68_ = l_IO_println___at___00main_spec__1___closed__1;
v___y_63_ = v___x_68_;
state = 1; continue;
}
}
1 => {
v___x_64_ = 10;
lean_inc_ref(v___y_63_);
v___x_65_ = lean_string_push(v___y_63_, v___x_64_);
v___x_66_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_65_);
return v___x_66_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_69_: *mut lean_object, mut v_a_70_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_71_: u8 = 0; let mut v_res_72_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_71_ = (lean_unbox(v_s_69_) as u8);
v_res_72_ = l_IO_println___at___00main_spec__1(v_s_boxed_71_);
return v_res_72_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__3(mut v_s_73_: f64) -> *mut lean_object{
let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: u32 = 0; let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); 
v___x_75_ = lean_float_to_string(v_s_73_);
v___x_76_ = 10;
v___x_77_ = lean_string_push(v___x_75_, v___x_76_);
v___x_78_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_77_);
return v___x_78_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__3___boxed(mut v_s_79_: *mut lean_object, mut v_a_80_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_81_: f64 = 0.0; let mut v_res_82_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_81_ = lean_unbox_float(v_s_79_);
lean_dec_ref(v_s_79_);
v_res_82_ = l_IO_println___at___00main_spec__3(v_s_boxed_81_);
return v_res_82_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2(mut v_s_83_: usize) -> *mut lean_object{
let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: u32 = 0; let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); 
v___x_85_ = lean_usize_to_nat(v_s_83_);
v___x_86_ = l_Nat_reprFast(v___x_85_);
v___x_87_ = 10;
v___x_88_ = lean_string_push(v___x_86_, v___x_87_);
v___x_89_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_88_);
return v___x_89_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2___boxed(mut v_s_90_: *mut lean_object, mut v_a_91_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_92_: usize = 0; let mut v_res_93_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_92_ = lean_unbox_usize(v_s_90_);
lean_dec(v_s_90_);
v_res_93_ = l_IO_println___at___00main_spec__2(v_s_boxed_92_);
return v_res_93_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_94_: u64) -> *mut lean_object{
let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: u32 = 0; let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); 
v___x_96_ = lean_uint64_to_nat(v_s_94_);
v___x_97_ = l_Nat_reprFast(v___x_96_);
v___x_98_ = 10;
v___x_99_ = lean_string_push(v___x_97_, v___x_98_);
v___x_100_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_99_);
return v___x_100_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_101_: *mut lean_object, mut v_a_102_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_103_: u64 = 0; let mut v_res_104_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_103_ = lean_unbox_uint64(v_s_101_);
lean_dec_ref(v_s_101_);
v_res_104_ = l_IO_println___at___00main_spec__0(v_s_boxed_103_);
return v_res_104_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_106_: u64 = 0; let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); 
v___x_106_ = l_test;
v___x_107_ = l_IO_println___at___00main_spec__0(v___x_106_);
if lean_obj_tag(v___x_107_) == 0 {
let mut v___x_108_: u8 = 0; let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_107_, 1);
v___x_108_ = l_testb;
v___x_109_ = l_IO_println___at___00main_spec__1(v___x_108_);
if lean_obj_tag(v___x_109_) == 0 {
let mut v___x_110_: usize = 0; let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_109_, 1);
v___x_110_ = l_testu;
v___x_111_ = l_IO_println___at___00main_spec__2(v___x_110_);
if lean_obj_tag(v___x_111_) == 0 {
let mut v___x_112_: f64 = 0.0; let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_111_, 1);
v___x_112_ = l_testf;
v___x_113_ = l_IO_println___at___00main_spec__3(v___x_112_);
if lean_obj_tag(v___x_113_) == 0 {
let mut v___x_114_: u32 = 0; let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_113_, 1);
v___x_114_ = l_test32;
v___x_115_ = l_IO_println___at___00main_spec__4(v___x_114_);
return v___x_115_;
} else {
return v___x_113_;
}
} else {
return v___x_111_;
}
} else {
return v___x_109_;
}
} else {
return v___x_107_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_116_: *mut lean_object) -> *mut lean_object{
let mut v_res_117_: *mut lean_object = core::ptr::null_mut(); 
v_res_117_ = _lean_main();
return v_res_117_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_initUnboxed(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2887224489____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
l_test = lean_unbox_uint64(lean_io_result_get_value(res));
lean_dec_ref(res);
res = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_3445265930____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
l_testb = lean_unbox(lean_io_result_get_value(res));
lean_dec_ref(res);
res = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2016441482____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
l_testu = lean_unbox_usize(lean_io_result_get_value(res));
lean_dec_ref(res);
l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_744502646____hygCtx___hyg_2_ = _init_l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_744502646____hygCtx___hyg_2_();
lean_mark_persistent(l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_744502646____hygCtx___hyg_2_);
res = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_744502646____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
l_testf = lean_unbox_float(lean_io_result_get_value(res));
lean_dec_ref(res);
l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_ = _init_l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_();
lean_mark_persistent(l___private_initUnboxed_0__initFn___boxed__const__1_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_);
res = l___private_initUnboxed_0__initFn_00___x40_initUnboxed_2208129052____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
l_test32 = lean_unbox_uint32(lean_io_result_get_value(res));
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_initUnboxed(1 /* builtin */);
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
