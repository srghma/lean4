// Lean compiler output
// Module: module
// Imports: Init Init Lean
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_lean::Lean::*;
use lean_lean::Lean::Elab::Exception::*;
use lean_init::Init::Prelude::*;
use lean_lean::Lean::Expr::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
pub static l_termMk__str___closed__0_value: lean_string_object<11> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 77, 107, 95, 115, 116, 114, 0]};
static mut l_termMk__str___closed__0: *mut lean_object = core::ptr::addr_of!(l_termMk__str___closed__0_value) as *mut lean_object;
pub static l_termMk__str___closed__1_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_termMk__str___closed__0_value) as *mut lean_object,10379945785527213554 as *mut lean_object] };
static mut l_termMk__str___closed__1: *mut lean_object = core::ptr::addr_of!(l_termMk__str___closed__1_value) as *mut lean_object;
pub static l_termMk__str___closed__2_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 95, 115, 116, 114, 0]};
static mut l_termMk__str___closed__2: *mut lean_object = core::ptr::addr_of!(l_termMk__str___closed__2_value) as *mut lean_object;
pub static l_termMk__str___closed__3_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 5 }, m_objs: [core::ptr::addr_of!(l_termMk__str___closed__2_value) as *mut lean_object] };
static mut l_termMk__str___closed__3: *mut lean_object = core::ptr::addr_of!(l_termMk__str___closed__3_value) as *mut lean_object;
pub static l_termMk__str___closed__4_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_termMk__str___closed__1_value) as *mut lean_object,((( 1024 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_termMk__str___closed__3_value) as *mut lean_object] };
static mut l_termMk__str___closed__4: *mut lean_object = core::ptr::addr_of!(l_termMk__str___closed__4_value) as *mut lean_object;
#[used]
#[no_mangle]
pub static mut l_termMk__str: *mut lean_object = core::ptr::addr_of!(l_termMk__str___closed__4_value) as *mut lean_object;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg___closed__0: *mut lean_object = core::ptr::null_mut();
pub static l___aux__module______elabRules__termMk__str__1___redArg___closed__0_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [119, 111, 114, 108, 100, 33, 0]};
static mut l___aux__module______elabRules__termMk__str__1___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l___aux__module______elabRules__termMk__str__1___redArg___closed__0_value) as *mut lean_object;
static mut l___aux__module______elabRules__termMk__str__1___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l___aux__module______elabRules__termMk__str__1___redArg___closed__1: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__0_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg___closed__0() -> *mut lean_object{
let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); 
v___x_12_ = lean_box(0);
v___x_13_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_14_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
return v___x_14_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg() -> *mut lean_object{
let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); 
v___x_16_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg___closed__0);
v___x_17_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg___boxed(mut v___y_18_: *mut lean_object) -> *mut lean_object{
let mut v_res_19_: *mut lean_object = core::ptr::null_mut(); 
v_res_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg();
return v_res_19_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0(mut v_00_u03b1_20_: *mut lean_object, mut v___y_21_: *mut lean_object, mut v___y_22_: *mut lean_object, mut v___y_23_: *mut lean_object, mut v___y_24_: *mut lean_object, mut v___y_25_: *mut lean_object, mut v___y_26_: *mut lean_object) -> *mut lean_object{
let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
v___x_28_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg();
return v___x_28_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___boxed(mut v_00_u03b1_29_: *mut lean_object, mut v___y_30_: *mut lean_object, mut v___y_31_: *mut lean_object, mut v___y_32_: *mut lean_object, mut v___y_33_: *mut lean_object, mut v___y_34_: *mut lean_object, mut v___y_35_: *mut lean_object, mut v___y_36_: *mut lean_object) -> *mut lean_object{
let mut v_res_37_: *mut lean_object = core::ptr::null_mut(); 
v_res_37_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0(v_00_u03b1_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
return v_res_37_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l___aux__module______elabRules__termMk__str__1___redArg___closed__1() -> *mut lean_object{
let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_39_ = l___aux__module______elabRules__termMk__str__1___redArg___closed__0;
v___x_40_ = l_Lean_mkStrLit(v___x_39_);
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn l___aux__module______elabRules__termMk__str__1___redArg(mut v_stx_41_: *mut lean_object, mut v_a_42_: *mut lean_object, mut v_a_43_: *mut lean_object, mut v_a_44_: *mut lean_object, mut v_a_45_: *mut lean_object, mut v_a_46_: *mut lean_object, mut v_a_47_: *mut lean_object) -> *mut lean_object{
let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: u8 = 0; 
v___x_49_ = l_termMk__str___closed__1;
v___x_50_ = l_Lean_Syntax_isOfKind(v_stx_41_, v___x_49_);
if v___x_50_ == 0 {
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
v___x_51_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__aux__module______elabRules__termMk__str__1_spec__0___redArg();
return v___x_51_;
} else {
let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); 
v___x_52_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__module______elabRules__termMk__str__1___redArg___closed__1), core::ptr::addr_of_mut!(l___aux__module______elabRules__termMk__str__1___redArg___closed__1_once), _init_l___aux__module______elabRules__termMk__str__1___redArg___closed__1);
v___x_53_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
#[no_mangle] pub unsafe extern "C" fn l___aux__module______elabRules__termMk__str__1___redArg___boxed(mut v_stx_54_: *mut lean_object, mut v_a_55_: *mut lean_object, mut v_a_56_: *mut lean_object, mut v_a_57_: *mut lean_object, mut v_a_58_: *mut lean_object, mut v_a_59_: *mut lean_object, mut v_a_60_: *mut lean_object, mut v_a_61_: *mut lean_object) -> *mut lean_object{
let mut v_res_62_: *mut lean_object = core::ptr::null_mut(); 
v_res_62_ = l___aux__module______elabRules__termMk__str__1___redArg(v_stx_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_62_;
}
#[no_mangle] pub unsafe extern "C" fn l___aux__module______elabRules__termMk__str__1(mut v_stx_63_: *mut lean_object, mut v_x_64_: *mut lean_object, mut v_a_65_: *mut lean_object, mut v_a_66_: *mut lean_object, mut v_a_67_: *mut lean_object, mut v_a_68_: *mut lean_object, mut v_a_69_: *mut lean_object, mut v_a_70_: *mut lean_object) -> *mut lean_object{
let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); 
v___x_72_ = l___aux__module______elabRules__termMk__str__1___redArg(v_stx_63_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
return v___x_72_;
}
#[no_mangle] pub unsafe extern "C" fn l___aux__module______elabRules__termMk__str__1___boxed(mut v_stx_73_: *mut lean_object, mut v_x_74_: *mut lean_object, mut v_a_75_: *mut lean_object, mut v_a_76_: *mut lean_object, mut v_a_77_: *mut lean_object, mut v_a_78_: *mut lean_object, mut v_a_79_: *mut lean_object, mut v_a_80_: *mut lean_object, mut v_a_81_: *mut lean_object) -> *mut lean_object{
let mut v_res_82_: *mut lean_object = core::ptr::null_mut(); 
v_res_82_ = l___aux__module______elabRules__termMk__str__1(v_stx_73_, v_x_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_x_74_);
return v_res_82_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_83_: *mut lean_object) -> *mut lean_object{
let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); 
v___x_85_ = lean_get_stdout();
v_putStr_86_ = lean_ctor_get(v___x_85_, 4);
lean_inc_ref(v_putStr_86_);
lean_dec_ref(v___x_85_);
v___x_87_ = lean_apply_2(v_putStr_86_, v_s_83_, lean_box(0));
return v___x_87_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_88_: *mut lean_object, mut v_a_89_: *mut lean_object) -> *mut lean_object{
let mut v_res_90_: *mut lean_object = core::ptr::null_mut(); 
v_res_90_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_88_);
return v_res_90_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_91_: *mut lean_object) -> *mut lean_object{
let mut v___x_93_: u32 = 0; let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); 
v___x_93_ = 10;
v___x_94_ = lean_string_push(v_s_91_, v___x_93_);
v___x_95_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_94_);
return v___x_95_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_96_: *mut lean_object, mut v_a_97_: *mut lean_object) -> *mut lean_object{
let mut v_res_98_: *mut lean_object = core::ptr::null_mut(); 
v_res_98_ = l_IO_println___at___00main_spec__0(v_s_96_);
return v_res_98_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
v___x_101_ = l_main___closed__0;
v___x_102_ = l_IO_println___at___00main_spec__0(v___x_101_);
return v___x_102_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_103_: *mut lean_object) -> *mut lean_object{
let mut v_res_104_: *mut lean_object = core::ptr::null_mut(); 
v_res_104_ = _lean_main();
return v_res_104_;
}
static mut _G_runtime_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn runtime_initialize_module(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_runtime_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_runtime_initialized = true;
res = runtime_initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn meta_initialize_module(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_meta_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_meta_initialized = true;
res = runtime_initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = runtime_initialize_Lean(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_module(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = runtime_initialize_module(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = meta_initialize_module(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return initialize_module(builtin);
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = runtime_initialize_module(1 /* builtin */);
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
