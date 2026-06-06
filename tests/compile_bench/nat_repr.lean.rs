// Lean compiler output
// Module: nat_repr
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_length(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<17> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [103, 105, 118, 101, 32, 117, 112, 112, 101, 114, 32, 98, 111, 117, 110, 100, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 18 }, m_objs: [core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__1___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: u32 = 0; let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = l_Nat_reprFast(v_s_9_);
v___x_12_ = 10;
v___x_13_ = lean_string_push(v___x_11_, v___x_12_);
v___x_14_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(v___x_13_);
return v___x_14_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_15_: *mut lean_object, mut v_a_16_: *mut lean_object) -> *mut lean_object{
let mut v_res_17_: *mut lean_object = core::ptr::null_mut(); 
v_res_17_ = l_IO_println___at___00main_spec__1(v_s_15_);
return v_res_17_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(mut v_upperBound_18_: *mut lean_object, mut v_a_19_: *mut lean_object, mut v_b_20_: *mut lean_object) -> *mut lean_object{
let mut v___x_22_: u8 = 0; let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_22_ = lean_nat_dec_lt(v_a_19_, v_upperBound_18_);
if v___x_22_ == 0 {
let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_19_);
v___x_23_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_23_, 0, v_b_20_);
return v___x_23_;
} else {
let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_a_19_);
v___x_24_ = l_Nat_reprFast(v_a_19_);
v___x_25_ = lean_string_length(v___x_24_);
lean_dec_ref(v___x_24_);
v___x_26_ = lean_nat_add(v_b_20_, v___x_25_);
lean_dec(v_b_20_);
v___x_27_ = lean_unsigned_to_nat(1);
v___x_28_ = lean_nat_add(v_a_19_, v___x_27_);
lean_dec(v_a_19_);
v_a_19_ = v___x_28_;
v_b_20_ = v___x_26_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg___boxed(mut v_upperBound_30_: *mut lean_object, mut v_a_31_: *mut lean_object, mut v_b_32_: *mut lean_object, mut v___y_33_: *mut lean_object) -> *mut lean_object{
let mut v_res_34_: *mut lean_object = core::ptr::null_mut(); 
v_res_34_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v_upperBound_30_, v_a_31_, v_b_32_);
lean_dec(v_upperBound_30_);
return v_res_34_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg(mut v_upperBound_35_: *mut lean_object, mut v_a_36_: *mut lean_object, mut v_b_37_: *mut lean_object) -> *mut lean_object{
let mut v___x_39_: u8 = 0; let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v_a_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_39_ = lean_nat_dec_lt(v_a_36_, v_upperBound_35_);
if v___x_39_ == 0 {
let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_36_);
v___x_40_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_40_, 0, v_b_37_);
return v___x_40_;
} else {
let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); 
v___x_41_ = lean_unsigned_to_nat(0);
v___x_42_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v_a_36_, v___x_41_, v_b_37_);
if lean_obj_tag(v___x_42_) == 0 {
let mut v_a_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_42_, 1);
v___x_44_ = lean_unsigned_to_nat(1);
v___x_45_ = lean_nat_add(v_a_36_, v___x_44_);
lean_dec(v_a_36_);
v_a_36_ = v___x_45_;
v_b_37_ = v_a_43_;
state = 0; continue;
} else {
lean_dec(v_a_36_);
return v___x_42_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___boxed(mut v_upperBound_47_: *mut lean_object, mut v_a_48_: *mut lean_object, mut v_b_49_: *mut lean_object, mut v___y_50_: *mut lean_object) -> *mut lean_object{
let mut v_res_51_: *mut lean_object = core::ptr::null_mut(); 
v_res_51_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg(v_upperBound_47_, v_a_48_, v_b_49_);
lean_dec(v_upperBound_47_);
return v_res_51_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_x_55_: *mut lean_object) -> *mut lean_object{
let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_60_: *mut lean_object = core::ptr::null_mut(); let mut v_head_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v_a_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v_a_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_72_: u8 = 0; let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_75_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_76_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_55_) == 1 {
let mut v_tail_60_: *mut lean_object = core::ptr::null_mut(); 
v_tail_60_ = lean_ctor_get(v_x_55_, 1);
if lean_obj_tag(v_tail_60_) == 0 {
let mut v_head_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); 
v_head_61_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_head_61_);
lean_dec_ref_known(v_x_55_, 2);
v___x_62_ = lean_unsigned_to_nat(0);
v___x_63_ = lean_string_utf8_byte_size(v_head_61_);
v___x_64_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_64_, 0, v_head_61_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_63_);
v___x_65_ = l_String_Slice_toNat_x21(v___x_64_);
lean_dec_ref_known(v___x_64_, 3);
v___x_66_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg(v___x_65_, v___x_62_, v___x_62_);
lean_dec(v___x_65_);
if lean_obj_tag(v___x_66_) == 0 {
let mut v_a_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = l_IO_println___at___00main_spec__1(v_a_67_);
return v___x_68_;
} else {
let mut v_a_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_72_: u8 = 0; let mut v_isSharedCheck_76_: u8 = 0; 
v_a_69_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_76_ = (!lean_is_exclusive(v___x_66_)) as u8;
if v_isSharedCheck_76_ == 0 {
v___x_71_ = v___x_66_;
v_isShared_72_ = v_isSharedCheck_76_;
state = 2; continue;
} else {
lean_inc(v_a_69_);
lean_dec(v___x_66_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
state = 2; continue;
}
}
} else {
lean_dec_ref_known(v_x_55_, 2);
state = 1; continue;
}
} else {
lean_dec(v_x_55_);
state = 1; continue;
}
}
1 => {
v___x_58_ = l_main___closed__1;
v___x_59_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
2 => {
if v_isShared_72_ == 0 {
v___x_74_ = v___x_71_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_75_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
state = 3; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_x_77_: *mut lean_object, mut v_a_78_: *mut lean_object) -> *mut lean_object{
let mut v_res_79_: *mut lean_object = core::ptr::null_mut(); 
v_res_79_ = _lean_main(v_x_77_);
return v_res_79_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0(mut v_upperBound_80_: *mut lean_object, mut v_inst_81_: *mut lean_object, mut v_R_82_: *mut lean_object, mut v_a_83_: *mut lean_object, mut v_b_84_: *mut lean_object, mut v_c_85_: *mut lean_object) -> *mut lean_object{
let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); 
v___x_87_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v_upperBound_80_, v_a_83_, v_b_84_);
return v___x_87_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___boxed(mut v_upperBound_88_: *mut lean_object, mut v_inst_89_: *mut lean_object, mut v_R_90_: *mut lean_object, mut v_a_91_: *mut lean_object, mut v_b_92_: *mut lean_object, mut v_c_93_: *mut lean_object, mut v___y_94_: *mut lean_object) -> *mut lean_object{
let mut v_res_95_: *mut lean_object = core::ptr::null_mut(); 
v_res_95_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0(v_upperBound_88_, v_inst_89_, v_R_90_, v_a_91_, v_b_92_, v_c_93_);
lean_dec(v_upperBound_88_);
return v_res_95_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__2(mut v_upperBound_96_: *mut lean_object, mut v_inst_97_: *mut lean_object, mut v_R_98_: *mut lean_object, mut v_a_99_: *mut lean_object, mut v_b_100_: *mut lean_object, mut v_c_101_: *mut lean_object) -> *mut lean_object{
let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); 
v___x_103_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg(v_upperBound_96_, v_a_99_, v_b_100_);
return v___x_103_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__2___boxed(mut v_upperBound_104_: *mut lean_object, mut v_inst_105_: *mut lean_object, mut v_R_106_: *mut lean_object, mut v_a_107_: *mut lean_object, mut v_b_108_: *mut lean_object, mut v_c_109_: *mut lean_object, mut v___y_110_: *mut lean_object) -> *mut lean_object{
let mut v_res_111_: *mut lean_object = core::ptr::null_mut(); 
v_res_111_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2(v_upperBound_104_, v_inst_105_, v_R_106_, v_a_107_, v_b_108_, v_c_109_);
lean_dec(v_upperBound_104_);
return v_res_111_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_nat__repr(builtin: u8) -> *mut lean_object {
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
  let res = initialize_nat__repr(1 /* builtin */);
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
