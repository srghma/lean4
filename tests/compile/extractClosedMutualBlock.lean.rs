// Lean compiler output
// Module: extractClosedMutualBlock
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[used]
#[no_mangle]
pub static mut l_instInhabitedFoo_default: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_instInhabitedFoo: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: u8 = 0;
pub static l_main___closed__2_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 69, 82, 77, 73, 78, 65, 76, 0]};
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
pub static l_main___closed__3_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [76, 65, 89, 69, 82, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_Foo_ctorIdx(mut v_x_1_: *mut lean_object) -> *mut lean_object{
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
#[no_mangle] pub unsafe extern "C" fn l_Foo_ctorIdx___boxed(mut v_x_4_: *mut lean_object) -> *mut lean_object{
let mut v_res_5_: *mut lean_object = core::ptr::null_mut(); 
v_res_5_ = l_Foo_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_ctorElim___redArg(mut v_t_6_: *mut lean_object, mut v_k_7_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_t_6_) == 0 {
let mut v_a_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); 
v_a_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_a_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_a_8_);
return v___x_9_;
} else {
return v_k_7_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_ctorElim(mut v_motive_10_: *mut lean_object, mut v_ctorIdx_11_: *mut lean_object, mut v_t_12_: *mut lean_object, mut v_h_13_: *mut lean_object, mut v_k_14_: *mut lean_object) -> *mut lean_object{
let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_15_ = l_Foo_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_ctorElim___boxed(mut v_motive_16_: *mut lean_object, mut v_ctorIdx_17_: *mut lean_object, mut v_t_18_: *mut lean_object, mut v_h_19_: *mut lean_object, mut v_k_20_: *mut lean_object) -> *mut lean_object{
let mut v_res_21_: *mut lean_object = core::ptr::null_mut(); 
v_res_21_ = l_Foo_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_mk_elim___redArg(mut v_t_22_: *mut lean_object, mut v_mk_23_: *mut lean_object) -> *mut lean_object{
let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); 
v___x_24_ = l_Foo_ctorElim___redArg(v_t_22_, v_mk_23_);
return v___x_24_;
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_mk_elim(mut v_motive_25_: *mut lean_object, mut v_t_26_: *mut lean_object, mut v_h_27_: *mut lean_object, mut v_mk_28_: *mut lean_object) -> *mut lean_object{
let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); 
v___x_29_ = l_Foo_ctorElim___redArg(v_t_26_, v_mk_28_);
return v___x_29_;
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_terminal_elim___redArg(mut v_t_30_: *mut lean_object, mut v_terminal_31_: *mut lean_object) -> *mut lean_object{
let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
v___x_32_ = l_Foo_ctorElim___redArg(v_t_30_, v_terminal_31_);
return v___x_32_;
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_terminal_elim(mut v_motive_33_: *mut lean_object, mut v_t_34_: *mut lean_object, mut v_h_35_: *mut lean_object, mut v_terminal_36_: *mut lean_object) -> *mut lean_object{
let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
v___x_37_ = l_Foo_ctorElim___redArg(v_t_34_, v_terminal_36_);
return v___x_37_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_instInhabitedFoo_default() -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); 
v___x_38_ = lean_box(1);
return v___x_38_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_instInhabitedFoo() -> *mut lean_object{
let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); 
v___x_39_ = lean_box(1);
return v___x_39_;
}
#[no_mangle] pub unsafe extern "C" fn l_odd___lam__0(mut v_i_40_: *mut lean_object) -> *mut lean_object{
let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); 
v___x_41_ = lean_box(0);
v___x_42_ = l_even(v___x_41_);
return v___x_42_;
}
#[no_mangle] pub unsafe extern "C" fn l_odd___lam__0___boxed(mut v_i_43_: *mut lean_object) -> *mut lean_object{
let mut v_res_44_: *mut lean_object = core::ptr::null_mut(); 
v_res_44_ = l_odd___lam__0(v_i_43_);
lean_dec(v_i_43_);
return v_res_44_;
}
#[no_mangle] pub unsafe extern "C" fn l_odd(mut v_x_45_: *mut lean_object) -> *mut lean_object{
let mut v___f_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); 
v___f_46_ = lean_alloc_closure(l_odd___lam__0___boxed as *mut core::ffi::c_void, 1, 0);
v___x_47_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_47_, 0, v___f_46_);
return v___x_47_;
}
#[no_mangle] pub unsafe extern "C" fn l_even___lam__0(mut v_i_48_: *mut lean_object) -> *mut lean_object{
let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); 
v___x_49_ = lean_box(0);
v___x_50_ = l_odd(v___x_49_);
return v___x_50_;
}
#[no_mangle] pub unsafe extern "C" fn l_even___lam__0___boxed(mut v_i_51_: *mut lean_object) -> *mut lean_object{
let mut v_res_52_: *mut lean_object = core::ptr::null_mut(); 
v_res_52_ = l_even___lam__0(v_i_51_);
lean_dec(v_i_51_);
return v_res_52_;
}
#[no_mangle] pub unsafe extern "C" fn l_even(mut v_x_53_: *mut lean_object) -> *mut lean_object{
let mut v___f_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); 
v___f_54_ = lean_alloc_closure(l_even___lam__0___boxed as *mut core::ffi::c_void, 1, 0);
v___x_55_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_55_, 0, v___f_54_);
return v___x_55_;
}
#[no_mangle] pub unsafe extern "C" fn l_hasLayer(mut v_f_56_: *mut lean_object) -> u8{
if lean_obj_tag(v_f_56_) == 0 {
let mut v___x_57_: u8 = 0; 
v___x_57_ = 1;
return v___x_57_;
} else {
let mut v___x_58_: u8 = 0; 
v___x_58_ = 0;
return v___x_58_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_hasLayer___boxed(mut v_f_59_: *mut lean_object) -> *mut lean_object{
let mut v_res_60_: u8 = 0; let mut v_r_61_: *mut lean_object = core::ptr::null_mut(); 
v_res_60_ = l_hasLayer(v_f_59_);
lean_dec(v_f_59_);
v_r_61_ = lean_box((v_res_60_) as usize);
return v_r_61_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_62_: *mut lean_object) -> *mut lean_object{
let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); 
v___x_64_ = lean_get_stdout();
v_putStr_65_ = lean_ctor_get(v___x_64_, 4);
lean_inc_ref(v_putStr_65_);
lean_dec_ref(v___x_64_);
v___x_66_ = lean_apply_2(v_putStr_65_, v_s_62_, lean_box(0));
return v___x_66_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_67_: *mut lean_object, mut v_a_68_: *mut lean_object) -> *mut lean_object{
let mut v_res_69_: *mut lean_object = core::ptr::null_mut(); 
v_res_69_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_67_);
return v_res_69_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_70_: *mut lean_object) -> *mut lean_object{
let mut v___x_72_: u32 = 0; let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); 
v___x_72_ = 10;
v___x_73_ = lean_string_push(v_s_70_, v___x_72_);
v___x_74_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_73_);
return v___x_74_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_75_: *mut lean_object, mut v_a_76_: *mut lean_object) -> *mut lean_object{
let mut v_res_77_: *mut lean_object = core::ptr::null_mut(); 
v_res_77_ = l_IO_println___at___00main_spec__0(v_s_75_);
return v_res_77_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); 
v___x_78_ = lean_box(0);
v___x_79_ = l_odd(v___x_78_);
return v___x_79_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> u8{
let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: u8 = 0; 
v___x_80_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_81_ = l_hasLayer(v___x_80_);
return v___x_81_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___y_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_91_: u8 = 0; let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_94_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_95_: u8 = 0; let mut v_unused_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: u8 = 0; let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_85_ = lean_box(0);
v___x_97_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
if v___x_97_ == 0 {
v___x_98_ = l_main___closed__2;
v___y_87_ = v___x_98_;
state = 1; continue;
} else {
v___x_99_ = l_main___closed__3;
v___y_87_ = v___x_99_;
state = 1; continue;
}
}
1 => {
lean_inc_ref(v___y_87_);
v___x_88_ = l_IO_println___at___00main_spec__0(v___y_87_);
if lean_obj_tag(v___x_88_) == 0 {
v_isSharedCheck_95_ = (!lean_is_exclusive(v___x_88_)) as u8;
if v_isSharedCheck_95_ == 0 {
v_unused_96_ = lean_ctor_get(v___x_88_, 0);
lean_dec(v_unused_96_);
v___x_90_ = v___x_88_;
v_isShared_91_ = v_isSharedCheck_95_;
state = 2; continue;
} else {
lean_dec(v___x_88_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
state = 2; continue;
}
} else {
return v___x_88_;
}
}
2 => {
if v_isShared_91_ == 0 {
lean_ctor_set(v___x_90_, 0, v___x_85_);
v___x_93_ = v___x_90_;
state = 3; continue;
} else {
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_85_);
v___x_93_ = v_reuseFailAlloc_94_;
state = 3; continue;
}
}
3 => {
return v___x_93_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_100_: *mut lean_object) -> *mut lean_object{
let mut v_res_101_: *mut lean_object = core::ptr::null_mut(); 
v_res_101_ = _lean_main();
return v_res_101_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_extractClosedMutualBlock(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_instInhabitedFoo_default = _init_l_instInhabitedFoo_default();
lean_mark_persistent(l_instInhabitedFoo_default);
l_instInhabitedFoo = _init_l_instInhabitedFoo();
lean_mark_persistent(l_instInhabitedFoo);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_extractClosedMutualBlock(1 /* builtin */);
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
