// Lean compiler output
// Module: closure_bug7
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
#[no_mangle] pub unsafe extern "C" fn l_f___lam__0(mut v_x7_30_: *mut lean_object, mut v_x6_31_: *mut lean_object, mut v_x5_32_: *mut lean_object, mut v_x4_33_: *mut lean_object, mut v_x3_34_: *mut lean_object, mut v_x2_35_: *mut lean_object, mut v_x1_36_: *mut lean_object, mut v_y_37_: *mut lean_object) -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); 
v___x_38_ = lean_box(0);
v___x_39_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_39_, 0, v_x7_30_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_40_, 0, v_x6_31_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_41_, 0, v_x5_32_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v___x_42_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_42_, 0, v_x4_33_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_43_, 0, v_x3_34_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_44_, 0, v_x2_35_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_45_, 0, v_x1_36_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = l_List_toString___at___00f_spec__0(v___x_45_);
return v___x_46_;
}
#[no_mangle] pub unsafe extern "C" fn l_f___lam__0___boxed(mut v_x7_47_: *mut lean_object, mut v_x6_48_: *mut lean_object, mut v_x5_49_: *mut lean_object, mut v_x4_50_: *mut lean_object, mut v_x3_51_: *mut lean_object, mut v_x2_52_: *mut lean_object, mut v_x1_53_: *mut lean_object, mut v_y_54_: *mut lean_object) -> *mut lean_object{
let mut v_res_55_: *mut lean_object = core::ptr::null_mut(); 
v_res_55_ = l_f___lam__0(v_x7_47_, v_x6_48_, v_x5_49_, v_x4_50_, v_x3_51_, v_x2_52_, v_x1_53_, v_y_54_);
lean_dec(v_y_54_);
return v_res_55_;
}
#[no_mangle] pub unsafe extern "C" fn l_f(mut v_x_56_: *mut lean_object) -> *mut lean_object{
let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v_x1_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v_x2_60_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v_x3_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v_x4_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v_x5_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v_x6_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v_x7_70_: *mut lean_object = core::ptr::null_mut(); let mut v___f_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); 
v___x_57_ = lean_unsigned_to_nat(1);
v_x1_58_ = lean_nat_add(v_x_56_, v___x_57_);
v___x_59_ = lean_unsigned_to_nat(2);
v_x2_60_ = lean_nat_add(v_x_56_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(3);
v_x3_62_ = lean_nat_add(v_x_56_, v___x_61_);
v___x_63_ = lean_unsigned_to_nat(4);
v_x4_64_ = lean_nat_add(v_x_56_, v___x_63_);
v___x_65_ = lean_unsigned_to_nat(5);
v_x5_66_ = lean_nat_add(v_x_56_, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(6);
v_x6_68_ = lean_nat_add(v_x_56_, v___x_67_);
v___x_69_ = lean_unsigned_to_nat(7);
v_x7_70_ = lean_nat_add(v_x_56_, v___x_69_);
v___f_71_ = lean_alloc_closure(l_f___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
lean_closure_set(v___f_71_, 0, v_x7_70_);
lean_closure_set(v___f_71_, 1, v_x6_68_);
lean_closure_set(v___f_71_, 2, v_x5_66_);
lean_closure_set(v___f_71_, 3, v_x4_64_);
lean_closure_set(v___f_71_, 4, v_x3_62_);
lean_closure_set(v___f_71_, 5, v_x2_60_);
lean_closure_set(v___f_71_, 6, v_x1_58_);
v___x_72_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_72_, 0, v_x_56_);
lean_ctor_set(v___x_72_, 1, v___f_71_);
return v___x_72_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_73_: *mut lean_object) -> *mut lean_object{
let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_76_: *mut lean_object = core::ptr::null_mut(); let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); 
v___x_75_ = lean_get_stdout();
v_putStr_76_ = lean_ctor_get(v___x_75_, 4);
lean_inc_ref(v_putStr_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = lean_apply_2(v_putStr_76_, v_s_73_, lean_box(0));
return v___x_77_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_78_: *mut lean_object, mut v_a_79_: *mut lean_object) -> *mut lean_object{
let mut v_res_80_: *mut lean_object = core::ptr::null_mut(); 
v_res_80_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_78_);
return v_res_80_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_81_: *mut lean_object) -> *mut lean_object{
let mut v___x_83_: u32 = 0; let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); 
v___x_83_ = 10;
v___x_84_ = lean_string_push(v_s_81_, v___x_83_);
v___x_85_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_84_);
return v___x_85_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_86_: *mut lean_object, mut v_a_87_: *mut lean_object) -> *mut lean_object{
let mut v_res_88_: *mut lean_object = core::ptr::null_mut(); 
v_res_88_ = l_IO_println___at___00main_spec__0(v_s_86_);
return v_res_88_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_90_: *mut lean_object) -> *mut lean_object{
let mut v___y_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v_head_103_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_xs_90_) == 0 {
v___x_102_ = l_main___closed__0;
v___y_93_ = v___x_102_;
state = 1; continue;
} else {
v_head_103_ = lean_ctor_get(v_xs_90_, 0);
lean_inc(v_head_103_);
lean_dec_ref_known(v_xs_90_, 2);
v___y_93_ = v_head_103_;
state = 1; continue;
}
}
1 => {
v___x_94_ = lean_unsigned_to_nat(0);
v___x_95_ = lean_string_utf8_byte_size(v___y_93_);
v___x_96_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_96_, 0, v___y_93_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_95_);
v___x_97_ = l_String_Slice_toNat_x21(v___x_96_);
lean_dec_ref_known(v___x_96_, 3);
lean_inc(v___x_97_);
v___x_98_ = l_f(v___x_97_);
v_snd_99_ = lean_ctor_get(v___x_98_, 1);
lean_inc(v_snd_99_);
lean_dec_ref(v___x_98_);
v___x_100_ = lean_apply_1(v_snd_99_, v___x_97_);
v___x_101_ = l_IO_println___at___00main_spec__0(v___x_100_);
return v___x_101_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_104_: *mut lean_object, mut v_a_105_: *mut lean_object) -> *mut lean_object{
let mut v_res_106_: *mut lean_object = core::ptr::null_mut(); 
v_res_106_ = _lean_main(v_xs_104_);
return v_res_106_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_closure__bug7(builtin: u8) -> *mut lean_object {
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
  let res = initialize_closure__bug7(1 /* builtin */);
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
