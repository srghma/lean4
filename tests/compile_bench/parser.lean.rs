// Lean compiler output
// Module: parser
// Imports: public import Init public meta import Init public import Lean.Parser.Module
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Lean_Parser_testParseFile(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_environment(_: u32) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<30> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [103, 105, 118, 101, 32, 102, 105, 108, 101, 32, 97, 110, 100, 32, 105, 116, 101, 114, 97, 116, 105, 111, 110, 32, 99, 111, 117, 110, 116, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 18 }, m_objs: [core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(mut v_upperBound_1_: *mut lean_object, mut v_head_2_: *mut lean_object, mut v_a_3_: *mut lean_object, mut v_a_4_: *mut lean_object, mut v_b_5_: *mut lean_object) -> *mut lean_object{
let mut v___x_7_: u8 = 0; let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v_a_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_17_: u8 = 0; let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_20_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_21_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_7_ = lean_nat_dec_lt(v_a_4_, v_upperBound_1_);
if v___x_7_ == 0 {
let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
lean_dec_ref(v_head_2_);
v___x_8_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_8_, 0, v_b_5_);
return v___x_8_;
} else {
let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_head_2_);
lean_inc_ref(v_a_3_);
v___x_9_ = l_Lean_Parser_testParseFile(v_a_3_, v_head_2_);
if lean_obj_tag(v___x_9_) == 0 {
let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_9_, 1);
v___x_10_ = lean_box(0);
v___x_11_ = lean_unsigned_to_nat(1);
v___x_12_ = lean_nat_add(v_a_4_, v___x_11_);
lean_dec(v_a_4_);
v_a_4_ = v___x_12_;
v_b_5_ = v___x_10_;
state = 0; continue;
} else {
let mut v_a_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_17_: u8 = 0; let mut v_isSharedCheck_21_: u8 = 0; 
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
lean_dec_ref(v_head_2_);
v_a_14_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_21_ = (!lean_is_exclusive(v___x_9_)) as u8;
if v_isSharedCheck_21_ == 0 {
v___x_16_ = v___x_9_;
v_isShared_17_ = v_isSharedCheck_21_;
state = 1; continue;
} else {
lean_inc(v_a_14_);
lean_dec(v___x_9_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
state = 1; continue;
}
}
}
}
1 => {
if v_isShared_17_ == 0 {
v___x_19_ = v___x_16_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_20_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_20_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_14_);
v___x_19_ = v_reuseFailAlloc_20_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg___boxed(mut v_upperBound_22_: *mut lean_object, mut v_head_23_: *mut lean_object, mut v_a_24_: *mut lean_object, mut v_a_25_: *mut lean_object, mut v_b_26_: *mut lean_object, mut v___y_27_: *mut lean_object) -> *mut lean_object{
let mut v_res_28_: *mut lean_object = core::ptr::null_mut(); 
v_res_28_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v_upperBound_22_, v_head_23_, v_a_24_, v_a_25_, v_b_26_);
lean_dec(v_upperBound_22_);
return v_res_28_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_x_32_: *mut lean_object) -> *mut lean_object{
let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_37_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_38_: *mut lean_object = core::ptr::null_mut(); let mut v_head_39_: *mut lean_object = core::ptr::null_mut(); let mut v_head_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: u32 = 0; let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v_a_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_52_: u8 = 0; let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_55_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_56_: u8 = 0; let mut v_unused_57_: *mut lean_object = core::ptr::null_mut(); let mut v_a_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_61_: u8 = 0; let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_64_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_65_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_32_) == 1 {
let mut v_tail_37_: *mut lean_object = core::ptr::null_mut(); 
v_tail_37_ = lean_ctor_get(v_x_32_, 1);
lean_inc(v_tail_37_);
if lean_obj_tag(v_tail_37_) == 1 {
let mut v_tail_38_: *mut lean_object = core::ptr::null_mut(); 
v_tail_38_ = lean_ctor_get(v_tail_37_, 1);
if lean_obj_tag(v_tail_38_) == 0 {
let mut v_head_39_: *mut lean_object = core::ptr::null_mut(); let mut v_head_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: u32 = 0; let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); 
v_head_39_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_head_39_);
lean_dec_ref_known(v_x_32_, 2);
v_head_40_ = lean_ctor_get(v_tail_37_, 0);
lean_inc(v_head_40_);
lean_dec_ref_known(v_tail_37_, 2);
v___x_41_ = 0;
v___x_42_ = lean_mk_empty_environment(v___x_41_);
if lean_obj_tag(v___x_42_) == 0 {
let mut v_a_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_42_, 1);
v___x_44_ = lean_unsigned_to_nat(0);
v___x_45_ = lean_string_utf8_byte_size(v_head_40_);
v___x_46_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_46_, 0, v_head_40_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
lean_ctor_set(v___x_46_, 2, v___x_45_);
v___x_47_ = l_String_Slice_toNat_x21(v___x_46_);
lean_dec_ref_known(v___x_46_, 3);
v___x_48_ = lean_box(0);
v___x_49_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v___x_47_, v_head_39_, v_a_43_, v___x_44_, v___x_48_);
lean_dec(v___x_47_);
if lean_obj_tag(v___x_49_) == 0 {
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_52_: u8 = 0; let mut v_isSharedCheck_56_: u8 = 0; 
v_isSharedCheck_56_ = (!lean_is_exclusive(v___x_49_)) as u8;
if v_isSharedCheck_56_ == 0 {
let mut v_unused_57_: *mut lean_object = core::ptr::null_mut(); 
v_unused_57_ = lean_ctor_get(v___x_49_, 0);
lean_dec(v_unused_57_);
v___x_51_ = v___x_49_;
v_isShared_52_ = v_isSharedCheck_56_;
state = 2; continue;
} else {
lean_dec(v___x_49_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
state = 2; continue;
}
} else {
return v___x_49_;
}
} else {
let mut v_a_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_61_: u8 = 0; let mut v_isSharedCheck_65_: u8 = 0; 
lean_dec(v_head_40_);
lean_dec(v_head_39_);
v_a_58_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_65_ = (!lean_is_exclusive(v___x_42_)) as u8;
if v_isSharedCheck_65_ == 0 {
v___x_60_ = v___x_42_;
v_isShared_61_ = v_isSharedCheck_65_;
state = 4; continue;
} else {
lean_inc(v_a_58_);
lean_dec(v___x_42_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
state = 4; continue;
}
}
} else {
lean_dec_ref_known(v_tail_37_, 2);
lean_dec_ref_known(v_x_32_, 2);
state = 1; continue;
}
} else {
lean_dec_ref_known(v_x_32_, 2);
lean_dec(v_tail_37_);
state = 1; continue;
}
} else {
lean_dec(v_x_32_);
state = 1; continue;
}
}
1 => {
v___x_35_ = l_main___closed__1;
v___x_36_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
2 => {
if v_isShared_52_ == 0 {
lean_ctor_set(v___x_51_, 0, v___x_48_);
v___x_54_ = v___x_51_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_55_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_48_);
v___x_54_ = v_reuseFailAlloc_55_;
state = 3; continue;
}
}
4 => {
if v_isShared_61_ == 0 {
v___x_63_ = v___x_60_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_64_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
state = 5; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_x_66_: *mut lean_object, mut v_a_67_: *mut lean_object) -> *mut lean_object{
let mut v_res_68_: *mut lean_object = core::ptr::null_mut(); 
v_res_68_ = _lean_main(v_x_66_);
return v_res_68_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0(mut v_upperBound_69_: *mut lean_object, mut v_head_70_: *mut lean_object, mut v_a_71_: *mut lean_object, mut v_inst_72_: *mut lean_object, mut v_R_73_: *mut lean_object, mut v_a_74_: *mut lean_object, mut v_b_75_: *mut lean_object, mut v_c_76_: *mut lean_object) -> *mut lean_object{
let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); 
v___x_78_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0___redArg(v_upperBound_69_, v_head_70_, v_a_71_, v_a_74_, v_b_75_);
return v___x_78_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__0___boxed(mut v_upperBound_79_: *mut lean_object, mut v_head_80_: *mut lean_object, mut v_a_81_: *mut lean_object, mut v_inst_82_: *mut lean_object, mut v_R_83_: *mut lean_object, mut v_a_84_: *mut lean_object, mut v_b_85_: *mut lean_object, mut v_c_86_: *mut lean_object, mut v___y_87_: *mut lean_object) -> *mut lean_object{
let mut v_res_88_: *mut lean_object = core::ptr::null_mut(); 
v_res_88_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__0(v_upperBound_79_, v_head_80_, v_a_81_, v_inst_82_, v_R_83_, v_a_84_, v_b_85_, v_c_86_);
lean_dec(v_upperBound_79_);
return v_res_88_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Parser_Module(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_parser(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
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
  let res = initialize_parser(1 /* builtin */);
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
