// Lean compiler output
// Module: rbmap_library
// Imports: public import Init public meta import Init public import Lean.Data.RBMap
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mul(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_RBNode_isRed___redArg(_: *mut lean_object) -> u8;
    fn l_Lean_RBNode_setBlack___redArg(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Lean_RBNode_depth___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_RBNode_isBlack___redArg(_: *mut lean_object) -> u8;
    fn l_Lean_RBNode_balRight___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_RBNode_appendTrees___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_RBNode_balLeft___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_compare(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_usize_dec_lt(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_IO_setRandSeed(_: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn l_IO_rand(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_size(_: *mut lean_object) -> usize;
    fn lean_nat_shiftr(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_usize_of_nat(_: *mut lean_object) -> usize;
    fn lean_usize_dec_eq(_: usize, _: usize) -> u8;
}
#[no_mangle] pub static l_check___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 82, 82, 79, 82, 0]};
static mut l_check___closed__0: *mut lean_object = core::ptr::addr_of!(l_check___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_depth___redArg___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_depth___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_depth___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_depth___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_tst1___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 101, 108, 108, 111, 0]};
static mut l_tst1___closed__0: *mut lean_object = core::ptr::addr_of!(l_tst1___closed__0_value) as *mut lean_object;
static mut l_tst1___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_tst1___closed__2_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [119, 111, 114, 108, 100, 0]};
static mut l_tst1___closed__2: *mut lean_object = core::ptr::addr_of!(l_tst1___closed__2_value) as *mut lean_object;
static mut l_tst1___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__4: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_tst1___closed__5_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_tst1___closed__5: *mut lean_object = core::ptr::addr_of!(l_tst1___closed__5_value) as *mut lean_object;
static mut l_tst1___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__6: u8 = 0;
static mut l_tst1___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__7: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_tst1___closed__8_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_tst1___closed__8: *mut lean_object = core::ptr::addr_of!(l_tst1___closed__8_value) as *mut lean_object;
static mut l_tst1___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__9: u8 = 0;
static mut l_tst1___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__10: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__11: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__12: u8 = 0;
static mut l_tst1___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__13: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__14: u8 = 0;
static mut l_tst2___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_tst2___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__1: u8 = 0;
static mut l_tst2___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_tst2___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__3: u8 = 0;
#[no_mangle] pub static l_tst2___closed__4_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [62, 62, 32, 0]};
static mut l_tst2___closed__4: *mut lean_object = core::ptr::addr_of!(l_tst2___closed__4_value) as *mut lean_object;
static mut l_tst2___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_tst2___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l_tst2___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__7: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_tst2___closed__8_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_tst2___closed__8: *mut lean_object = core::ptr::addr_of!(l_tst2___closed__8_value) as *mut lean_object;
static mut l_tst2___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__9: *mut lean_object = core::ptr::null_mut();
static mut l_tst2___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__10: *mut lean_object = core::ptr::null_mut();
static mut l_tst2___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst2___closed__11: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_tst2___closed__12_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 5000 as usize) << 1) | 1) as *mut lean_object,((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_tst2___closed__12: *mut lean_object = core::ptr::addr_of!(l_tst2___closed__12_value) as *mut lean_object;
#[no_mangle] pub static l_tst3___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_tst3___closed__0: *mut lean_object = core::ptr::addr_of!(l_tst3___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_tst3___closed__1_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 115, 116, 51, 32, 115, 105, 122, 101, 58, 32, 0]};
static mut l_tst3___closed__1: *mut lean_object = core::ptr::addr_of!(l_tst3___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_tst3___closed__2_value: lean_string_object<20> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [116, 115, 116, 51, 32, 97, 102, 116, 101, 114, 44, 32, 100, 101, 112, 116, 104, 58, 32, 0]};
static mut l_tst3___closed__2: *mut lean_object = core::ptr::addr_of!(l_tst3___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_tst3___closed__3_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 32, 115, 105, 122, 101, 58, 32, 0]};
static mut l_tst3___closed__3: *mut lean_object = core::ptr::addr_of!(l_tst3___closed__3_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00check_spec__0_spec__0(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00check_spec__0_spec__0___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00IO_println___at___00check_spec__0_spec__0(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00check_spec__0(mut v_s_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: u32 = 0; let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = 10;
v___x_12_ = lean_string_push(v_s_9_, v___x_11_);
v___x_13_ = l_IO_print___at___00IO_println___at___00check_spec__0_spec__0(v___x_12_);
return v___x_13_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00check_spec__0___boxed(mut v_s_14_: *mut lean_object, mut v_a_15_: *mut lean_object) -> *mut lean_object{
let mut v_res_16_: *mut lean_object = core::ptr::null_mut(); 
v_res_16_ = l_IO_println___at___00check_spec__0(v_s_14_);
return v_res_16_;
}
#[no_mangle] pub unsafe extern "C" fn l_check(mut v_b_18_: u8) -> *mut lean_object{
if v_b_18_ == 0 {
let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); 
v___x_20_ = l_check___closed__0;
v___x_21_ = l_IO_println___at___00check_spec__0(v___x_20_);
return v___x_21_;
} else {
let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); 
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_check___boxed(mut v_b_24_: *mut lean_object, mut v_a_25_: *mut lean_object) -> *mut lean_object{
let mut v_b_boxed_26_: u8 = 0; let mut v_res_27_: *mut lean_object = core::ptr::null_mut(); 
v_b_boxed_26_ = (lean_unbox(v_b_24_) as u8);
v_res_27_ = l_check(v_b_boxed_26_);
return v_res_27_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_fold___at___00sz_spec__0___redArg(mut v_x_28_: *mut lean_object, mut v_x_29_: *mut lean_object) -> *mut lean_object{
let mut v_lchild_30_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_29_) == 0 {
return v_x_28_;
} else {
let mut v_lchild_30_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
v_lchild_30_ = lean_ctor_get(v_x_29_, 0);
v_rchild_31_ = lean_ctor_get(v_x_29_, 3);
v___x_32_ = l_Lean_RBNode_fold___at___00sz_spec__0___redArg(v_x_28_, v_lchild_30_);
v___x_33_ = lean_unsigned_to_nat(1);
v___x_34_ = lean_nat_add(v___x_32_, v___x_33_);
lean_dec(v___x_32_);
v_x_28_ = v___x_34_;
v_x_29_ = v_rchild_31_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_fold___at___00sz_spec__0___redArg___boxed(mut v_x_36_: *mut lean_object, mut v_x_37_: *mut lean_object) -> *mut lean_object{
let mut v_res_38_: *mut lean_object = core::ptr::null_mut(); 
v_res_38_ = l_Lean_RBNode_fold___at___00sz_spec__0___redArg(v_x_36_, v_x_37_);
lean_dec(v_x_37_);
return v_res_38_;
}
#[no_mangle] pub unsafe extern "C" fn l_sz___redArg(mut v_m_39_: *mut lean_object) -> *mut lean_object{
let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); 
v___x_40_ = lean_unsigned_to_nat(0);
v___x_41_ = l_Lean_RBNode_fold___at___00sz_spec__0___redArg(v___x_40_, v_m_39_);
return v___x_41_;
}
#[no_mangle] pub unsafe extern "C" fn l_sz___redArg___boxed(mut v_m_42_: *mut lean_object) -> *mut lean_object{
let mut v_res_43_: *mut lean_object = core::ptr::null_mut(); 
v_res_43_ = l_sz___redArg(v_m_42_);
lean_dec(v_m_42_);
return v_res_43_;
}
#[no_mangle] pub unsafe extern "C" fn l_sz(mut v_00_u03b1_44_: *mut lean_object, mut v_00_u03b2_45_: *mut lean_object, mut v_cmp_46_: *mut lean_object, mut v_m_47_: *mut lean_object) -> *mut lean_object{
let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); 
v___x_48_ = l_sz___redArg(v_m_47_);
return v___x_48_;
}
#[no_mangle] pub unsafe extern "C" fn l_sz___boxed(mut v_00_u03b1_49_: *mut lean_object, mut v_00_u03b2_50_: *mut lean_object, mut v_cmp_51_: *mut lean_object, mut v_m_52_: *mut lean_object) -> *mut lean_object{
let mut v_res_53_: *mut lean_object = core::ptr::null_mut(); 
v_res_53_ = l_sz(v_00_u03b1_49_, v_00_u03b2_50_, v_cmp_51_, v_m_52_);
lean_dec(v_m_52_);
lean_dec_ref(v_cmp_51_);
return v_res_53_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_fold___at___00sz_spec__0(mut v_00_u03b1_54_: *mut lean_object, mut v_00_u03b2_55_: *mut lean_object, mut v_x_56_: *mut lean_object, mut v_x_57_: *mut lean_object) -> *mut lean_object{
let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); 
v___x_58_ = l_Lean_RBNode_fold___at___00sz_spec__0___redArg(v_x_56_, v_x_57_);
return v___x_58_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_fold___at___00sz_spec__0___boxed(mut v_00_u03b1_59_: *mut lean_object, mut v_00_u03b2_60_: *mut lean_object, mut v_x_61_: *mut lean_object, mut v_x_62_: *mut lean_object) -> *mut lean_object{
let mut v_res_63_: *mut lean_object = core::ptr::null_mut(); 
v_res_63_ = l_Lean_RBNode_fold___at___00sz_spec__0(v_00_u03b1_59_, v_00_u03b2_60_, v_x_61_, v_x_62_);
lean_dec(v_x_62_);
return v_res_63_;
}
#[no_mangle] pub unsafe extern "C" fn l_depth___redArg___lam__0(mut v___y_64_: *mut lean_object, mut v___y_65_: *mut lean_object) -> *mut lean_object{
let mut v___x_66_: u8 = 0; 
v___x_66_ = lean_nat_dec_le(v___y_64_, v___y_65_);
if v___x_66_ == 0 {
lean_inc(v___y_64_);
return v___y_64_;
} else {
lean_inc(v___y_65_);
return v___y_65_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_depth___redArg___lam__0___boxed(mut v___y_67_: *mut lean_object, mut v___y_68_: *mut lean_object) -> *mut lean_object{
let mut v_res_69_: *mut lean_object = core::ptr::null_mut(); 
v_res_69_ = l_depth___redArg___lam__0(v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec(v___y_67_);
return v_res_69_;
}
#[no_mangle] pub unsafe extern "C" fn l_depth___redArg(mut v_m_71_: *mut lean_object) -> *mut lean_object{
let mut v___f_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); 
v___f_72_ = l_depth___redArg___closed__0;
v___x_73_ = l_Lean_RBNode_depth___redArg(v___f_72_, v_m_71_);
return v___x_73_;
}
#[no_mangle] pub unsafe extern "C" fn l_depth___redArg___boxed(mut v_m_74_: *mut lean_object) -> *mut lean_object{
let mut v_res_75_: *mut lean_object = core::ptr::null_mut(); 
v_res_75_ = l_depth___redArg(v_m_74_);
lean_dec(v_m_74_);
return v_res_75_;
}
#[no_mangle] pub unsafe extern "C" fn l_depth(mut v_00_u03b1_76_: *mut lean_object, mut v_00_u03b2_77_: *mut lean_object, mut v_cmp_78_: *mut lean_object, mut v_m_79_: *mut lean_object) -> *mut lean_object{
let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); 
v___x_80_ = l_depth___redArg(v_m_79_);
return v___x_80_;
}
#[no_mangle] pub unsafe extern "C" fn l_depth___boxed(mut v_00_u03b1_81_: *mut lean_object, mut v_00_u03b2_82_: *mut lean_object, mut v_cmp_83_: *mut lean_object, mut v_m_84_: *mut lean_object) -> *mut lean_object{
let mut v_res_85_: *mut lean_object = core::ptr::null_mut(); 
v_res_85_ = l_depth(v_00_u03b1_81_, v_00_u03b2_82_, v_cmp_83_, v_m_84_);
lean_dec(v_m_84_);
lean_dec_ref(v_cmp_83_);
return v_res_85_;
}
#[no_mangle] pub unsafe extern "C" fn l_Option_instBEq_beq___at___00tst1_spec__2(mut v_x_86_: *mut lean_object, mut v_x_87_: *mut lean_object) -> u8{
if lean_obj_tag(v_x_86_) == 0 {
if lean_obj_tag(v_x_87_) == 0 {
let mut v___x_88_: u8 = 0; 
v___x_88_ = 1;
return v___x_88_;
} else {
let mut v___x_89_: u8 = 0; 
v___x_89_ = 0;
return v___x_89_;
}
} else {
if lean_obj_tag(v_x_87_) == 0 {
let mut v___x_90_: u8 = 0; 
v___x_90_ = 0;
return v___x_90_;
} else {
let mut v_val_91_: *mut lean_object = core::ptr::null_mut(); let mut v_val_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: u8 = 0; 
v_val_91_ = lean_ctor_get(v_x_86_, 0);
v_val_92_ = lean_ctor_get(v_x_87_, 0);
v___x_93_ = lean_nat_dec_eq(v_val_91_, v_val_92_);
return v___x_93_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Option_instBEq_beq___at___00tst1_spec__2___boxed(mut v_x_94_: *mut lean_object, mut v_x_95_: *mut lean_object) -> *mut lean_object{
let mut v_res_96_: u8 = 0; let mut v_r_97_: *mut lean_object = core::ptr::null_mut(); 
v_res_96_ = l_Option_instBEq_beq___at___00tst1_spec__2(v_x_94_, v_x_95_);
lean_dec(v_x_95_);
lean_dec(v_x_94_);
v_r_97_ = lean_box((v_res_96_) as usize);
return v_r_97_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg(mut v_x_98_: *mut lean_object, mut v_x_99_: *mut lean_object) -> *mut lean_object{
let mut v_lchild_100_: *mut lean_object = core::ptr::null_mut(); let mut v_key_101_: *mut lean_object = core::ptr::null_mut(); let mut v_val_102_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_106_: u8 = 0; let mut v___x_107_: u8 = 0; let mut v___x_108_: u8 = 0; let mut v___x_109_: u8 = 0; let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: u8 = 0; let mut v___x_118_: u8 = 0; let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_125_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_99_) == 0 {
return v_x_99_;
} else {
let mut v_lchild_100_: *mut lean_object = core::ptr::null_mut(); let mut v_key_101_: *mut lean_object = core::ptr::null_mut(); let mut v_val_102_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_106_: u8 = 0; let mut v_isSharedCheck_125_: u8 = 0; 
v_lchild_100_ = lean_ctor_get(v_x_99_, 0);
v_key_101_ = lean_ctor_get(v_x_99_, 1);
v_val_102_ = lean_ctor_get(v_x_99_, 2);
v_rchild_103_ = lean_ctor_get(v_x_99_, 3);
v_isSharedCheck_125_ = (!lean_is_exclusive(v_x_99_)) as u8;
if v_isSharedCheck_125_ == 0 {
v___x_105_ = v_x_99_;
v_isShared_106_ = v_isSharedCheck_125_;
state = 1; continue;
} else {
lean_inc(v_rchild_103_);
lean_inc(v_val_102_);
lean_inc(v_key_101_);
lean_inc(v_lchild_100_);
lean_dec(v_x_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_125_;
state = 1; continue;
}
}
}
1 => {
v___x_107_ = lean_string_compare(v_x_98_, v_key_101_);
match v___x_107_
{
0 => {
let mut v___x_108_: u8 = 0; 
v___x_108_ = l_Lean_RBNode_isBlack___redArg(v_lchild_100_);
if v___x_108_ == 0 {
let mut v___x_109_: u8 = 0; let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); 
v___x_109_ = 0;
v___x_110_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg(v_x_98_, v_lchild_100_);
if v_isShared_106_ == 0 {
lean_ctor_set(v___x_105_, 0, v___x_110_);
v___x_112_ = v___x_105_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_113_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_key_101_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_val_102_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_rchild_103_);
v___x_112_ = v_reuseFailAlloc_113_;
state = 2; continue;
}
} else {
let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_105_);
v___x_114_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg(v_x_98_, v_lchild_100_);
v___x_115_ = l_Lean_RBNode_balLeft___redArg(v___x_114_, v_key_101_, v_val_102_, v_rchild_103_);
return v___x_115_;
}
}
1 => {
let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_105_);
lean_dec(v_val_102_);
lean_dec(v_key_101_);
v___x_116_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_100_, v_rchild_103_);
return v___x_116_;
}
_ => {
let mut v___x_117_: u8 = 0; 
v___x_117_ = l_Lean_RBNode_isBlack___redArg(v_rchild_103_);
if v___x_117_ == 0 {
let mut v___x_118_: u8 = 0; let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); 
v___x_118_ = 0;
v___x_119_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg(v_x_98_, v_rchild_103_);
if v_isShared_106_ == 0 {
lean_ctor_set(v___x_105_, 3, v___x_119_);
v___x_121_ = v___x_105_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_122_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_lchild_100_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_key_101_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_val_102_);
lean_ctor_set(v_reuseFailAlloc_122_, 3, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
state = 3; continue;
}
} else {
let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_105_);
v___x_123_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg(v_x_98_, v_rchild_103_);
v___x_124_ = l_Lean_RBNode_balRight___redArg(v_lchild_100_, v_key_101_, v_val_102_, v___x_123_);
return v___x_124_;
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg___boxed(mut v_x_126_: *mut lean_object, mut v_x_127_: *mut lean_object) -> *mut lean_object{
let mut v_res_128_: *mut lean_object = core::ptr::null_mut(); 
v_res_128_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg(v_x_126_, v_x_127_);
lean_dec_ref(v_x_126_);
return v_res_128_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_erase___at___00tst1_spec__3___redArg(mut v_x_129_: *mut lean_object, mut v_t_130_: *mut lean_object) -> *mut lean_object{
let mut v_t_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); 
v_t_131_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg(v_x_129_, v_t_130_);
v___x_132_ = l_Lean_RBNode_setBlack___redArg(v_t_131_);
return v___x_132_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_erase___at___00tst1_spec__3___redArg___boxed(mut v_x_133_: *mut lean_object, mut v_t_134_: *mut lean_object) -> *mut lean_object{
let mut v_res_135_: *mut lean_object = core::ptr::null_mut(); 
v_res_135_ = l_Lean_RBNode_erase___at___00tst1_spec__3___redArg(v_x_133_, v_t_134_);
lean_dec_ref(v_x_133_);
return v_res_135_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_find___at___00tst1_spec__1___redArg(mut v_x_136_: *mut lean_object, mut v_x_137_: *mut lean_object) -> *mut lean_object{
let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v_lchild_139_: *mut lean_object = core::ptr::null_mut(); let mut v_key_140_: *mut lean_object = core::ptr::null_mut(); let mut v_val_141_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: u8 = 0; let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_136_) == 0 {
let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); 
v___x_138_ = lean_box(0);
return v___x_138_;
} else {
let mut v_lchild_139_: *mut lean_object = core::ptr::null_mut(); let mut v_key_140_: *mut lean_object = core::ptr::null_mut(); let mut v_val_141_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: u8 = 0; 
v_lchild_139_ = lean_ctor_get(v_x_136_, 0);
v_key_140_ = lean_ctor_get(v_x_136_, 1);
v_val_141_ = lean_ctor_get(v_x_136_, 2);
v_rchild_142_ = lean_ctor_get(v_x_136_, 3);
v___x_143_ = lean_string_compare(v_x_137_, v_key_140_);
match v___x_143_
{
0 => {
v_x_136_ = v_lchild_139_;
state = 0; continue;
}
1 => {
let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_val_141_);
v___x_145_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_145_, 0, v_val_141_);
return v___x_145_;
}
_ => {
v_x_136_ = v_rchild_142_;
state = 0; continue;
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_find___at___00tst1_spec__1___redArg___boxed(mut v_x_147_: *mut lean_object, mut v_x_148_: *mut lean_object) -> *mut lean_object{
let mut v_res_149_: *mut lean_object = core::ptr::null_mut(); 
v_res_149_ = l_Lean_RBNode_find___at___00tst1_spec__1___redArg(v_x_147_, v_x_148_);
lean_dec_ref(v_x_148_);
lean_dec(v_x_147_);
return v_res_149_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0___redArg(mut v_x_150_: *mut lean_object, mut v_x_151_: *mut lean_object, mut v_x_152_: *mut lean_object) -> *mut lean_object{
let mut v___x_153_: u8 = 0; let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); let mut v_color_155_: u8 = 0; let mut v_lchild_156_: *mut lean_object = core::ptr::null_mut(); let mut v_key_157_: *mut lean_object = core::ptr::null_mut(); let mut v_val_158_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_162_: u8 = 0; let mut v___x_163_: u8 = 0; let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_174_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_175_: u8 = 0; let mut v_lchild_176_: *mut lean_object = core::ptr::null_mut(); let mut v_key_177_: *mut lean_object = core::ptr::null_mut(); let mut v_val_178_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_182_: u8 = 0; let mut v___x_183_: u8 = 0; let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v_color_185_: u8 = 0; let mut v_lchild_186_: *mut lean_object = core::ptr::null_mut(); let mut v_key_187_: *mut lean_object = core::ptr::null_mut(); let mut v_val_188_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_189_: *mut lean_object = core::ptr::null_mut(); let mut v_a_191_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_192_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_193_: *mut lean_object = core::ptr::null_mut(); let mut v_b_194_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_195_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_196_: *mut lean_object = core::ptr::null_mut(); let mut v_c_197_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_198_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_199_: *mut lean_object = core::ptr::null_mut(); let mut v_d_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_205_: *mut lean_object = core::ptr::null_mut(); let mut v_color_206_: u8 = 0; let mut v_lchild_207_: *mut lean_object = core::ptr::null_mut(); let mut v_key_208_: *mut lean_object = core::ptr::null_mut(); let mut v_val_209_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_210_: *mut lean_object = core::ptr::null_mut(); let mut v_color_211_: u8 = 0; let mut v_lchild_212_: *mut lean_object = core::ptr::null_mut(); let mut v_key_213_: *mut lean_object = core::ptr::null_mut(); let mut v_val_214_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_218_: u8 = 0; let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_221_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_222_: u8 = 0; let mut v_unused_223_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_224_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_225_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_226_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_229_: u8 = 0; let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_232_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_233_: u8 = 0; let mut v_unused_234_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_235_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_236_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_237_: *mut lean_object = core::ptr::null_mut(); let mut v_color_238_: u8 = 0; let mut v_lchild_239_: *mut lean_object = core::ptr::null_mut(); let mut v_key_240_: *mut lean_object = core::ptr::null_mut(); let mut v_val_241_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_242_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_245_: u8 = 0; let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_248_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_249_: u8 = 0; let mut v_unused_250_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_251_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_252_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_253_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); let mut v___x_255_: *mut lean_object = core::ptr::null_mut(); let mut v___x_257_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_258_: *mut lean_object = core::ptr::null_mut(); let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_261_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v_color_263_: u8 = 0; let mut v_lchild_264_: *mut lean_object = core::ptr::null_mut(); let mut v_key_265_: *mut lean_object = core::ptr::null_mut(); let mut v_val_266_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_267_: *mut lean_object = core::ptr::null_mut(); let mut v_a_269_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_270_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_271_: *mut lean_object = core::ptr::null_mut(); let mut v_b_272_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_273_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_274_: *mut lean_object = core::ptr::null_mut(); let mut v_c_275_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_276_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_277_: *mut lean_object = core::ptr::null_mut(); let mut v_d_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: *mut lean_object = core::ptr::null_mut(); let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_283_: *mut lean_object = core::ptr::null_mut(); let mut v_color_284_: u8 = 0; let mut v_lchild_285_: *mut lean_object = core::ptr::null_mut(); let mut v_key_286_: *mut lean_object = core::ptr::null_mut(); let mut v_val_287_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_288_: *mut lean_object = core::ptr::null_mut(); let mut v_color_289_: u8 = 0; let mut v_lchild_290_: *mut lean_object = core::ptr::null_mut(); let mut v_key_291_: *mut lean_object = core::ptr::null_mut(); let mut v_val_292_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_295_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_296_: u8 = 0; let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_299_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_300_: u8 = 0; let mut v_unused_301_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_302_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_303_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_306_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_307_: u8 = 0; let mut v___x_309_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_310_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_311_: u8 = 0; let mut v_unused_312_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_313_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_314_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_315_: *mut lean_object = core::ptr::null_mut(); let mut v_color_316_: u8 = 0; let mut v_lchild_317_: *mut lean_object = core::ptr::null_mut(); let mut v_key_318_: *mut lean_object = core::ptr::null_mut(); let mut v_val_319_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_320_: *mut lean_object = core::ptr::null_mut(); let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_323_: u8 = 0; let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_326_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_327_: u8 = 0; let mut v_unused_328_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_329_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_330_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_336_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_337_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_150_) == 0 {
let mut v___x_153_: u8 = 0; let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); 
v___x_153_ = 0;
v___x_154_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_154_, 0, v_x_150_);
lean_ctor_set(v___x_154_, 1, v_x_151_);
lean_ctor_set(v___x_154_, 2, v_x_152_);
lean_ctor_set(v___x_154_, 3, v_x_150_);
lean_ctor_set_uint8(v___x_154_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v___x_153_);
return v___x_154_;
} else {
let mut v_color_155_: u8 = 0; 
v_color_155_ = lean_ctor_get_uint8(v_x_150_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_155_ == 0 {
let mut v_lchild_156_: *mut lean_object = core::ptr::null_mut(); let mut v_key_157_: *mut lean_object = core::ptr::null_mut(); let mut v_val_158_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_162_: u8 = 0; let mut v_isSharedCheck_175_: u8 = 0; 
v_lchild_156_ = lean_ctor_get(v_x_150_, 0);
v_key_157_ = lean_ctor_get(v_x_150_, 1);
v_val_158_ = lean_ctor_get(v_x_150_, 2);
v_rchild_159_ = lean_ctor_get(v_x_150_, 3);
v_isSharedCheck_175_ = (!lean_is_exclusive(v_x_150_)) as u8;
if v_isSharedCheck_175_ == 0 {
v___x_161_ = v_x_150_;
v_isShared_162_ = v_isSharedCheck_175_;
state = 1; continue;
} else {
lean_inc(v_rchild_159_);
lean_inc(v_val_158_);
lean_inc(v_key_157_);
lean_inc(v_lchild_156_);
lean_dec(v_x_150_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_175_;
state = 1; continue;
}
} else {
let mut v_lchild_176_: *mut lean_object = core::ptr::null_mut(); let mut v_key_177_: *mut lean_object = core::ptr::null_mut(); let mut v_val_178_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_182_: u8 = 0; let mut v_isSharedCheck_337_: u8 = 0; 
v_lchild_176_ = lean_ctor_get(v_x_150_, 0);
v_key_177_ = lean_ctor_get(v_x_150_, 1);
v_val_178_ = lean_ctor_get(v_x_150_, 2);
v_rchild_179_ = lean_ctor_get(v_x_150_, 3);
v_isSharedCheck_337_ = (!lean_is_exclusive(v_x_150_)) as u8;
if v_isSharedCheck_337_ == 0 {
v___x_181_ = v_x_150_;
v_isShared_182_ = v_isSharedCheck_337_;
state = 5; continue;
} else {
lean_inc(v_rchild_179_);
lean_inc(v_val_178_);
lean_inc(v_key_177_);
lean_inc(v_lchild_176_);
lean_dec(v_x_150_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_337_;
state = 5; continue;
}
}
}
}
1 => {
v___x_163_ = lean_string_compare(v_x_151_, v_key_157_);
match v___x_163_
{
0 => {
let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); 
v___x_164_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0___redArg(v_lchild_156_, v_x_151_, v_x_152_);
if v_isShared_162_ == 0 {
lean_ctor_set(v___x_161_, 0, v___x_164_);
v___x_166_ = v___x_161_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_167_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_key_157_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_val_158_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_rchild_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_167_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
v___x_166_ = v_reuseFailAlloc_167_;
state = 2; continue;
}
}
1 => {
let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_val_158_);
lean_dec(v_key_157_);
if v_isShared_162_ == 0 {
lean_ctor_set(v___x_161_, 2, v_x_152_);
lean_ctor_set(v___x_161_, 1, v_x_151_);
v___x_169_ = v___x_161_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_170_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_lchild_156_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_x_151_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_x_152_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_rchild_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
v___x_169_ = v_reuseFailAlloc_170_;
state = 3; continue;
}
}
_ => {
let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: *mut lean_object = core::ptr::null_mut(); 
v___x_171_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0___redArg(v_rchild_159_, v_x_151_, v_x_152_);
if v_isShared_162_ == 0 {
lean_ctor_set(v___x_161_, 3, v___x_171_);
v___x_173_ = v___x_161_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_174_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_lchild_156_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_key_157_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_val_158_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___x_171_);
lean_ctor_set_uint8(v_reuseFailAlloc_174_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
v___x_173_ = v_reuseFailAlloc_174_;
state = 4; continue;
}
}
}
}
5 => {
v___x_183_ = lean_string_compare(v_x_151_, v_key_177_);
match v___x_183_
{
0 => {
let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); 
v___x_184_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0___redArg(v_lchild_176_, v_x_151_, v_x_152_);
if lean_obj_tag(v___x_184_) == 1 {
let mut v_color_185_: u8 = 0; let mut v_lchild_186_: *mut lean_object = core::ptr::null_mut(); let mut v_key_187_: *mut lean_object = core::ptr::null_mut(); let mut v_val_188_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_189_: *mut lean_object = core::ptr::null_mut(); let mut v_a_191_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_192_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_193_: *mut lean_object = core::ptr::null_mut(); let mut v_b_194_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_195_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_196_: *mut lean_object = core::ptr::null_mut(); let mut v_c_197_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_198_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_199_: *mut lean_object = core::ptr::null_mut(); let mut v_d_200_: *mut lean_object = core::ptr::null_mut(); 
v_color_185_ = lean_ctor_get_uint8(v___x_184_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
v_lchild_186_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_lchild_186_);
v_key_187_ = lean_ctor_get(v___x_184_, 1);
lean_inc(v_key_187_);
v_val_188_ = lean_ctor_get(v___x_184_, 2);
lean_inc(v_val_188_);
v_rchild_189_ = lean_ctor_get(v___x_184_, 3);
lean_inc(v_rchild_189_);
if v_color_185_ == 0 {
if lean_obj_tag(v_lchild_186_) == 1 {
let mut v_color_206_: u8 = 0; 
v_color_206_ = lean_ctor_get_uint8(v_lchild_186_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_206_ == 0 {
let mut v_lchild_207_: *mut lean_object = core::ptr::null_mut(); let mut v_key_208_: *mut lean_object = core::ptr::null_mut(); let mut v_val_209_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_210_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_184_, 4);
v_lchild_207_ = lean_ctor_get(v_lchild_186_, 0);
lean_inc(v_lchild_207_);
v_key_208_ = lean_ctor_get(v_lchild_186_, 1);
lean_inc(v_key_208_);
v_val_209_ = lean_ctor_get(v_lchild_186_, 2);
lean_inc(v_val_209_);
v_rchild_210_ = lean_ctor_get(v_lchild_186_, 3);
lean_inc(v_rchild_210_);
lean_dec_ref_known(v_lchild_186_, 4);
v_a_191_ = v_lchild_207_;
v_kx_192_ = v_key_208_;
v_vx_193_ = v_val_209_;
v_b_194_ = v_rchild_210_;
v_ky_195_ = v_key_187_;
v_vy_196_ = v_val_188_;
v_c_197_ = v_rchild_189_;
v_kz_198_ = v_key_177_;
v_vz_199_ = v_val_178_;
v_d_200_ = v_rchild_179_;
state = 6; continue;
} else {
if lean_obj_tag(v_rchild_189_) == 1 {
let mut v_color_211_: u8 = 0; 
v_color_211_ = lean_ctor_get_uint8(v_rchild_189_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_211_ == 0 {
let mut v_lchild_212_: *mut lean_object = core::ptr::null_mut(); let mut v_key_213_: *mut lean_object = core::ptr::null_mut(); let mut v_val_214_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_215_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_184_, 4);
v_lchild_212_ = lean_ctor_get(v_rchild_189_, 0);
lean_inc(v_lchild_212_);
v_key_213_ = lean_ctor_get(v_rchild_189_, 1);
lean_inc(v_key_213_);
v_val_214_ = lean_ctor_get(v_rchild_189_, 2);
lean_inc(v_val_214_);
v_rchild_215_ = lean_ctor_get(v_rchild_189_, 3);
lean_inc(v_rchild_215_);
lean_dec_ref_known(v_rchild_189_, 4);
v_a_191_ = v_lchild_186_;
v_kx_192_ = v_key_187_;
v_vx_193_ = v_val_188_;
v_b_194_ = v_lchild_212_;
v_ky_195_ = v_key_213_;
v_vy_196_ = v_val_214_;
v_c_197_ = v_rchild_215_;
v_kz_198_ = v_key_177_;
v_vz_199_ = v_val_178_;
v_d_200_ = v_rchild_179_;
state = 6; continue;
} else {
let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_218_: u8 = 0; let mut v_isSharedCheck_222_: u8 = 0; 
lean_dec_ref_known(v_lchild_186_, 4);
lean_dec(v_val_188_);
lean_dec(v_key_187_);
lean_del_object(v___x_181_);
v_isSharedCheck_222_ = (!lean_is_exclusive(v_rchild_189_)) as u8;
if v_isSharedCheck_222_ == 0 {
let mut v_unused_223_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_224_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_225_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_226_: *mut lean_object = core::ptr::null_mut(); 
v_unused_223_ = lean_ctor_get(v_rchild_189_, 3);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_rchild_189_, 2);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_rchild_189_, 1);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_rchild_189_, 0);
lean_dec(v_unused_226_);
v___x_217_ = v_rchild_189_;
v_isShared_218_ = v_isSharedCheck_222_;
state = 8; continue;
} else {
lean_dec(v_rchild_189_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
state = 8; continue;
}
}
} else {
let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_229_: u8 = 0; let mut v_isSharedCheck_233_: u8 = 0; 
lean_dec(v_rchild_189_);
lean_dec(v_val_188_);
lean_dec(v_key_187_);
lean_del_object(v___x_181_);
v_isSharedCheck_233_ = (!lean_is_exclusive(v_lchild_186_)) as u8;
if v_isSharedCheck_233_ == 0 {
let mut v_unused_234_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_235_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_236_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_237_: *mut lean_object = core::ptr::null_mut(); 
v_unused_234_ = lean_ctor_get(v_lchild_186_, 3);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_lchild_186_, 2);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_lchild_186_, 1);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_lchild_186_, 0);
lean_dec(v_unused_237_);
v___x_228_ = v_lchild_186_;
v_isShared_229_ = v_isSharedCheck_233_;
state = 10; continue;
} else {
lean_dec(v_lchild_186_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
state = 10; continue;
}
}
}
} else {
if lean_obj_tag(v_rchild_189_) == 1 {
let mut v_color_238_: u8 = 0; 
v_color_238_ = lean_ctor_get_uint8(v_rchild_189_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_238_ == 0 {
let mut v_lchild_239_: *mut lean_object = core::ptr::null_mut(); let mut v_key_240_: *mut lean_object = core::ptr::null_mut(); let mut v_val_241_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_242_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_184_, 4);
v_lchild_239_ = lean_ctor_get(v_rchild_189_, 0);
lean_inc(v_lchild_239_);
v_key_240_ = lean_ctor_get(v_rchild_189_, 1);
lean_inc(v_key_240_);
v_val_241_ = lean_ctor_get(v_rchild_189_, 2);
lean_inc(v_val_241_);
v_rchild_242_ = lean_ctor_get(v_rchild_189_, 3);
lean_inc(v_rchild_242_);
lean_dec_ref_known(v_rchild_189_, 4);
v_a_191_ = v_lchild_186_;
v_kx_192_ = v_key_187_;
v_vx_193_ = v_val_188_;
v_b_194_ = v_lchild_239_;
v_ky_195_ = v_key_240_;
v_vy_196_ = v_val_241_;
v_c_197_ = v_rchild_242_;
v_kz_198_ = v_key_177_;
v_vz_199_ = v_val_178_;
v_d_200_ = v_rchild_179_;
state = 6; continue;
} else {
let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_245_: u8 = 0; let mut v_isSharedCheck_249_: u8 = 0; 
lean_dec(v_val_188_);
lean_dec(v_key_187_);
lean_dec(v_lchild_186_);
lean_del_object(v___x_181_);
v_isSharedCheck_249_ = (!lean_is_exclusive(v_rchild_189_)) as u8;
if v_isSharedCheck_249_ == 0 {
let mut v_unused_250_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_251_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_252_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_253_: *mut lean_object = core::ptr::null_mut(); 
v_unused_250_ = lean_ctor_get(v_rchild_189_, 3);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_rchild_189_, 2);
lean_dec(v_unused_251_);
v_unused_252_ = lean_ctor_get(v_rchild_189_, 1);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_rchild_189_, 0);
lean_dec(v_unused_253_);
v___x_244_ = v_rchild_189_;
v_isShared_245_ = v_isSharedCheck_249_;
state = 12; continue;
} else {
lean_dec(v_rchild_189_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
state = 12; continue;
}
}
} else {
let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_189_);
lean_dec(v_val_188_);
lean_dec(v_key_187_);
lean_dec(v_lchild_186_);
lean_del_object(v___x_181_);
v___x_254_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_254_, 0, v___x_184_);
lean_ctor_set(v___x_254_, 1, v_key_177_);
lean_ctor_set(v___x_254_, 2, v_val_178_);
lean_ctor_set(v___x_254_, 3, v_rchild_179_);
lean_ctor_set_uint8(v___x_254_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
return v___x_254_;
}
}
} else {
let mut v___x_255_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_189_);
lean_dec(v_val_188_);
lean_dec(v_key_187_);
lean_dec(v_lchild_186_);
lean_del_object(v___x_181_);
v___x_255_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_255_, 0, v___x_184_);
lean_ctor_set(v___x_255_, 1, v_key_177_);
lean_ctor_set(v___x_255_, 2, v_val_178_);
lean_ctor_set(v___x_255_, 3, v_rchild_179_);
lean_ctor_set_uint8(v___x_255_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
return v___x_255_;
}
} else {
let mut v___x_257_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_182_ == 0 {
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_257_ = v___x_181_;
state = 14; continue;
} else {
let mut v_reuseFailAlloc_258_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_key_177_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_val_178_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_rchild_179_);
lean_ctor_set_uint8(v_reuseFailAlloc_258_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
v___x_257_ = v_reuseFailAlloc_258_;
state = 14; continue;
}
}
}
1 => {
let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_val_178_);
lean_dec(v_key_177_);
if v_isShared_182_ == 0 {
lean_ctor_set(v___x_181_, 2, v_x_152_);
lean_ctor_set(v___x_181_, 1, v_x_151_);
v___x_260_ = v___x_181_;
state = 15; continue;
} else {
let mut v_reuseFailAlloc_261_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_lchild_176_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_x_151_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_x_152_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_rchild_179_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
v___x_260_ = v_reuseFailAlloc_261_;
state = 15; continue;
}
}
_ => {
let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); 
v___x_262_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0___redArg(v_rchild_179_, v_x_151_, v_x_152_);
if lean_obj_tag(v___x_262_) == 1 {
let mut v_color_263_: u8 = 0; let mut v_lchild_264_: *mut lean_object = core::ptr::null_mut(); let mut v_key_265_: *mut lean_object = core::ptr::null_mut(); let mut v_val_266_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_267_: *mut lean_object = core::ptr::null_mut(); let mut v_a_269_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_270_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_271_: *mut lean_object = core::ptr::null_mut(); let mut v_b_272_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_273_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_274_: *mut lean_object = core::ptr::null_mut(); let mut v_c_275_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_276_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_277_: *mut lean_object = core::ptr::null_mut(); let mut v_d_278_: *mut lean_object = core::ptr::null_mut(); 
v_color_263_ = lean_ctor_get_uint8(v___x_262_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
v_lchild_264_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_lchild_264_);
v_key_265_ = lean_ctor_get(v___x_262_, 1);
lean_inc(v_key_265_);
v_val_266_ = lean_ctor_get(v___x_262_, 2);
lean_inc(v_val_266_);
v_rchild_267_ = lean_ctor_get(v___x_262_, 3);
lean_inc(v_rchild_267_);
if v_color_263_ == 0 {
if lean_obj_tag(v_lchild_264_) == 1 {
let mut v_color_284_: u8 = 0; 
v_color_284_ = lean_ctor_get_uint8(v_lchild_264_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_284_ == 0 {
let mut v_lchild_285_: *mut lean_object = core::ptr::null_mut(); let mut v_key_286_: *mut lean_object = core::ptr::null_mut(); let mut v_val_287_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_288_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_262_, 4);
v_lchild_285_ = lean_ctor_get(v_lchild_264_, 0);
lean_inc(v_lchild_285_);
v_key_286_ = lean_ctor_get(v_lchild_264_, 1);
lean_inc(v_key_286_);
v_val_287_ = lean_ctor_get(v_lchild_264_, 2);
lean_inc(v_val_287_);
v_rchild_288_ = lean_ctor_get(v_lchild_264_, 3);
lean_inc(v_rchild_288_);
lean_dec_ref_known(v_lchild_264_, 4);
v_a_269_ = v_lchild_176_;
v_kx_270_ = v_key_177_;
v_vx_271_ = v_val_178_;
v_b_272_ = v_lchild_285_;
v_ky_273_ = v_key_286_;
v_vy_274_ = v_val_287_;
v_c_275_ = v_rchild_288_;
v_kz_276_ = v_key_265_;
v_vz_277_ = v_val_266_;
v_d_278_ = v_rchild_267_;
state = 16; continue;
} else {
if lean_obj_tag(v_rchild_267_) == 1 {
let mut v_color_289_: u8 = 0; 
v_color_289_ = lean_ctor_get_uint8(v_rchild_267_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_289_ == 0 {
let mut v_lchild_290_: *mut lean_object = core::ptr::null_mut(); let mut v_key_291_: *mut lean_object = core::ptr::null_mut(); let mut v_val_292_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_293_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_262_, 4);
v_lchild_290_ = lean_ctor_get(v_rchild_267_, 0);
lean_inc(v_lchild_290_);
v_key_291_ = lean_ctor_get(v_rchild_267_, 1);
lean_inc(v_key_291_);
v_val_292_ = lean_ctor_get(v_rchild_267_, 2);
lean_inc(v_val_292_);
v_rchild_293_ = lean_ctor_get(v_rchild_267_, 3);
lean_inc(v_rchild_293_);
lean_dec_ref_known(v_rchild_267_, 4);
v_a_269_ = v_lchild_176_;
v_kx_270_ = v_key_177_;
v_vx_271_ = v_val_178_;
v_b_272_ = v_lchild_264_;
v_ky_273_ = v_key_265_;
v_vy_274_ = v_val_266_;
v_c_275_ = v_lchild_290_;
v_kz_276_ = v_key_291_;
v_vz_277_ = v_val_292_;
v_d_278_ = v_rchild_293_;
state = 16; continue;
} else {
let mut v___x_295_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_296_: u8 = 0; let mut v_isSharedCheck_300_: u8 = 0; 
lean_dec_ref_known(v_lchild_264_, 4);
lean_dec(v_val_266_);
lean_dec(v_key_265_);
lean_del_object(v___x_181_);
v_isSharedCheck_300_ = (!lean_is_exclusive(v_rchild_267_)) as u8;
if v_isSharedCheck_300_ == 0 {
let mut v_unused_301_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_302_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_303_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_304_: *mut lean_object = core::ptr::null_mut(); 
v_unused_301_ = lean_ctor_get(v_rchild_267_, 3);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_rchild_267_, 2);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_rchild_267_, 1);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_rchild_267_, 0);
lean_dec(v_unused_304_);
v___x_295_ = v_rchild_267_;
v_isShared_296_ = v_isSharedCheck_300_;
state = 18; continue;
} else {
lean_dec(v_rchild_267_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
state = 18; continue;
}
}
} else {
let mut v___x_306_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_307_: u8 = 0; let mut v_isSharedCheck_311_: u8 = 0; 
lean_dec(v_rchild_267_);
lean_dec(v_val_266_);
lean_dec(v_key_265_);
lean_del_object(v___x_181_);
v_isSharedCheck_311_ = (!lean_is_exclusive(v_lchild_264_)) as u8;
if v_isSharedCheck_311_ == 0 {
let mut v_unused_312_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_313_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_314_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_315_: *mut lean_object = core::ptr::null_mut(); 
v_unused_312_ = lean_ctor_get(v_lchild_264_, 3);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_lchild_264_, 2);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_lchild_264_, 1);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_lchild_264_, 0);
lean_dec(v_unused_315_);
v___x_306_ = v_lchild_264_;
v_isShared_307_ = v_isSharedCheck_311_;
state = 20; continue;
} else {
lean_dec(v_lchild_264_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
state = 20; continue;
}
}
}
} else {
if lean_obj_tag(v_rchild_267_) == 1 {
let mut v_color_316_: u8 = 0; 
v_color_316_ = lean_ctor_get_uint8(v_rchild_267_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_316_ == 0 {
let mut v_lchild_317_: *mut lean_object = core::ptr::null_mut(); let mut v_key_318_: *mut lean_object = core::ptr::null_mut(); let mut v_val_319_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_320_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_262_, 4);
v_lchild_317_ = lean_ctor_get(v_rchild_267_, 0);
lean_inc(v_lchild_317_);
v_key_318_ = lean_ctor_get(v_rchild_267_, 1);
lean_inc(v_key_318_);
v_val_319_ = lean_ctor_get(v_rchild_267_, 2);
lean_inc(v_val_319_);
v_rchild_320_ = lean_ctor_get(v_rchild_267_, 3);
lean_inc(v_rchild_320_);
lean_dec_ref_known(v_rchild_267_, 4);
v_a_269_ = v_lchild_176_;
v_kx_270_ = v_key_177_;
v_vx_271_ = v_val_178_;
v_b_272_ = v_lchild_264_;
v_ky_273_ = v_key_265_;
v_vy_274_ = v_val_266_;
v_c_275_ = v_lchild_317_;
v_kz_276_ = v_key_318_;
v_vz_277_ = v_val_319_;
v_d_278_ = v_rchild_320_;
state = 16; continue;
} else {
let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_323_: u8 = 0; let mut v_isSharedCheck_327_: u8 = 0; 
lean_dec(v_val_266_);
lean_dec(v_key_265_);
lean_dec(v_lchild_264_);
lean_del_object(v___x_181_);
v_isSharedCheck_327_ = (!lean_is_exclusive(v_rchild_267_)) as u8;
if v_isSharedCheck_327_ == 0 {
let mut v_unused_328_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_329_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_330_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_331_: *mut lean_object = core::ptr::null_mut(); 
v_unused_328_ = lean_ctor_get(v_rchild_267_, 3);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_rchild_267_, 2);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_rchild_267_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_rchild_267_, 0);
lean_dec(v_unused_331_);
v___x_322_ = v_rchild_267_;
v_isShared_323_ = v_isSharedCheck_327_;
state = 22; continue;
} else {
lean_dec(v_rchild_267_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
state = 22; continue;
}
}
} else {
let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_267_);
lean_dec(v_val_266_);
lean_dec(v_key_265_);
lean_dec(v_lchild_264_);
lean_del_object(v___x_181_);
v___x_332_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_332_, 0, v_lchild_176_);
lean_ctor_set(v___x_332_, 1, v_key_177_);
lean_ctor_set(v___x_332_, 2, v_val_178_);
lean_ctor_set(v___x_332_, 3, v___x_262_);
lean_ctor_set_uint8(v___x_332_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
return v___x_332_;
}
}
} else {
let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_267_);
lean_dec(v_val_266_);
lean_dec(v_key_265_);
lean_dec(v_lchild_264_);
lean_del_object(v___x_181_);
v___x_333_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_333_, 0, v_lchild_176_);
lean_ctor_set(v___x_333_, 1, v_key_177_);
lean_ctor_set(v___x_333_, 2, v_val_178_);
lean_ctor_set(v___x_333_, 3, v___x_262_);
lean_ctor_set_uint8(v___x_333_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
return v___x_333_;
}
} else {
let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_182_ == 0 {
lean_ctor_set(v___x_181_, 3, v___x_262_);
v___x_335_ = v___x_181_;
state = 24; continue;
} else {
let mut v_reuseFailAlloc_336_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_lchild_176_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_key_177_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_val_178_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v___x_262_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_155_);
v___x_335_ = v_reuseFailAlloc_336_;
state = 24; continue;
}
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_insert___at___00tst1_spec__0___redArg(mut v_t_338_: *mut lean_object, mut v_k_339_: *mut lean_object, mut v_v_340_: *mut lean_object) -> *mut lean_object{
let mut v___x_341_: u8 = 0; 
v___x_341_ = l_Lean_RBNode_isRed___redArg(v_t_338_);
if v___x_341_ == 0 {
let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); 
v___x_342_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0___redArg(v_t_338_, v_k_339_, v_v_340_);
return v___x_342_;
} else {
let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_344_: *mut lean_object = core::ptr::null_mut(); 
v___x_343_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0___redArg(v_t_338_, v_k_339_, v_v_340_);
v___x_344_ = l_Lean_RBNode_setBlack___redArg(v___x_343_);
return v___x_344_;
}
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__1() -> *mut lean_object{
let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); 
v___x_346_ = lean_unsigned_to_nat(0);
v___x_347_ = l_tst1___closed__0;
v___x_348_ = lean_box(0);
v___x_349_ = l_Lean_RBNode_insert___at___00tst1_spec__0___redArg(v___x_348_, v___x_347_, v___x_346_);
return v___x_349_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__3() -> *mut lean_object{
let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_353_: *mut lean_object = core::ptr::null_mut(); let mut v___x_354_: *mut lean_object = core::ptr::null_mut(); 
v___x_351_ = lean_unsigned_to_nat(1);
v___x_352_ = l_tst1___closed__2;
v___x_353_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_354_ = l_Lean_RBNode_insert___at___00tst1_spec__0___redArg(v___x_353_, v___x_352_, v___x_351_);
return v___x_354_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__4() -> *mut lean_object{
let mut v___x_355_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_357_: *mut lean_object = core::ptr::null_mut(); 
v___x_355_ = l_tst1___closed__0;
v___x_356_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_357_ = l_Lean_RBNode_find___at___00tst1_spec__1___redArg(v___x_356_, v___x_355_);
return v___x_357_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__6() -> u8{
let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: u8 = 0; 
v___x_360_ = l_tst1___closed__5;
v___x_361_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__4), core::ptr::addr_of_mut!(l_tst1___closed__4_once), _init_l_tst1___closed__4);
v___x_362_ = l_Option_instBEq_beq___at___00tst1_spec__2(v___x_361_, v___x_360_);
return v___x_362_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__7() -> *mut lean_object{
let mut v___x_363_: *mut lean_object = core::ptr::null_mut(); let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); let mut v___x_365_: *mut lean_object = core::ptr::null_mut(); 
v___x_363_ = l_tst1___closed__2;
v___x_364_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_365_ = l_Lean_RBNode_find___at___00tst1_spec__1___redArg(v___x_364_, v___x_363_);
return v___x_365_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__9() -> u8{
let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: u8 = 0; 
v___x_368_ = l_tst1___closed__8;
v___x_369_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__7), core::ptr::addr_of_mut!(l_tst1___closed__7_once), _init_l_tst1___closed__7);
v___x_370_ = l_Option_instBEq_beq___at___00tst1_spec__2(v___x_369_, v___x_368_);
return v___x_370_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__10() -> *mut lean_object{
let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); let mut v___x_372_: *mut lean_object = core::ptr::null_mut(); let mut v___x_373_: *mut lean_object = core::ptr::null_mut(); 
v___x_371_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_372_ = l_tst1___closed__0;
v___x_373_ = l_Lean_RBNode_erase___at___00tst1_spec__3___redArg(v___x_372_, v___x_371_);
return v___x_373_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__11() -> *mut lean_object{
let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_375_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); 
v___x_374_ = l_tst1___closed__0;
v___x_375_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__10), core::ptr::addr_of_mut!(l_tst1___closed__10_once), _init_l_tst1___closed__10);
v___x_376_ = l_Lean_RBNode_find___at___00tst1_spec__1___redArg(v___x_375_, v___x_374_);
return v___x_376_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__12() -> u8{
let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_379_: u8 = 0; 
v___x_377_ = lean_box(0);
v___x_378_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__11), core::ptr::addr_of_mut!(l_tst1___closed__11_once), _init_l_tst1___closed__11);
v___x_379_ = l_Option_instBEq_beq___at___00tst1_spec__2(v___x_378_, v___x_377_);
return v___x_379_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__13() -> *mut lean_object{
let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); 
v___x_380_ = l_tst1___closed__2;
v___x_381_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__10), core::ptr::addr_of_mut!(l_tst1___closed__10_once), _init_l_tst1___closed__10);
v___x_382_ = l_Lean_RBNode_find___at___00tst1_spec__1___redArg(v___x_381_, v___x_380_);
return v___x_382_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__14() -> u8{
let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v___x_384_: *mut lean_object = core::ptr::null_mut(); let mut v___x_385_: u8 = 0; 
v___x_383_ = l_tst1___closed__8;
v___x_384_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__13), core::ptr::addr_of_mut!(l_tst1___closed__13_once), _init_l_tst1___closed__13);
v___x_385_ = l_Option_instBEq_beq___at___00tst1_spec__2(v___x_384_, v___x_383_);
return v___x_385_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst1() -> *mut lean_object{
let mut v___x_387_: u8 = 0; let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); let mut v___x_389_: u8 = 0; let mut v___x_390_: *mut lean_object = core::ptr::null_mut(); let mut v___x_391_: u8 = 0; let mut v___x_392_: *mut lean_object = core::ptr::null_mut(); let mut v___x_393_: u8 = 0; let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_396_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_397_: u8 = 0; let mut v___x_398_: *mut lean_object = core::ptr::null_mut(); let mut v___x_400_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_401_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_402_: u8 = 0; let mut v_unused_403_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_387_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__6), core::ptr::addr_of_mut!(l_tst1___closed__6_once), _init_l_tst1___closed__6);
v___x_388_ = l_check(v___x_387_);
if lean_obj_tag(v___x_388_) == 0 {
let mut v___x_389_: u8 = 0; let mut v___x_390_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_388_, 1);
v___x_389_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__9), core::ptr::addr_of_mut!(l_tst1___closed__9_once), _init_l_tst1___closed__9);
v___x_390_ = l_check(v___x_389_);
if lean_obj_tag(v___x_390_) == 0 {
let mut v___x_391_: u8 = 0; let mut v___x_392_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_390_, 1);
v___x_391_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__12), core::ptr::addr_of_mut!(l_tst1___closed__12_once), _init_l_tst1___closed__12);
v___x_392_ = l_check(v___x_391_);
if lean_obj_tag(v___x_392_) == 0 {
let mut v___x_393_: u8 = 0; let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_392_, 1);
v___x_393_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__14), core::ptr::addr_of_mut!(l_tst1___closed__14_once), _init_l_tst1___closed__14);
v___x_394_ = l_check(v___x_393_);
if lean_obj_tag(v___x_394_) == 0 {
let mut v___x_396_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_397_: u8 = 0; let mut v_isSharedCheck_402_: u8 = 0; 
v_isSharedCheck_402_ = (!lean_is_exclusive(v___x_394_)) as u8;
if v_isSharedCheck_402_ == 0 {
let mut v_unused_403_: *mut lean_object = core::ptr::null_mut(); 
v_unused_403_ = lean_ctor_get(v___x_394_, 0);
lean_dec(v_unused_403_);
v___x_396_ = v___x_394_;
v_isShared_397_ = v_isSharedCheck_402_;
state = 1; continue;
} else {
lean_dec(v___x_394_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
state = 1; continue;
}
} else {
return v___x_394_;
}
} else {
return v___x_392_;
}
} else {
return v___x_390_;
}
} else {
return v___x_388_;
}
}
1 => {
v___x_398_ = lean_box(0);
if v_isShared_397_ == 0 {
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_400_ = v___x_396_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_401_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_tst1___boxed(mut v_a_404_: *mut lean_object) -> *mut lean_object{
let mut v_res_405_: *mut lean_object = core::ptr::null_mut(); 
v_res_405_ = l_tst1();
return v_res_405_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_insert___at___00tst1_spec__0(mut v_00_u03b2_406_: *mut lean_object, mut v_t_407_: *mut lean_object, mut v_k_408_: *mut lean_object, mut v_v_409_: *mut lean_object) -> *mut lean_object{
let mut v___x_410_: *mut lean_object = core::ptr::null_mut(); 
v___x_410_ = l_Lean_RBNode_insert___at___00tst1_spec__0___redArg(v_t_407_, v_k_408_, v_v_409_);
return v___x_410_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_find___at___00tst1_spec__1(mut v_00_u03b2_411_: *mut lean_object, mut v_x_412_: *mut lean_object, mut v_x_413_: *mut lean_object) -> *mut lean_object{
let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); 
v___x_414_ = l_Lean_RBNode_find___at___00tst1_spec__1___redArg(v_x_412_, v_x_413_);
return v___x_414_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_find___at___00tst1_spec__1___boxed(mut v_00_u03b2_415_: *mut lean_object, mut v_x_416_: *mut lean_object, mut v_x_417_: *mut lean_object) -> *mut lean_object{
let mut v_res_418_: *mut lean_object = core::ptr::null_mut(); 
v_res_418_ = l_Lean_RBNode_find___at___00tst1_spec__1(v_00_u03b2_415_, v_x_416_, v_x_417_);
lean_dec_ref(v_x_417_);
lean_dec(v_x_416_);
return v_res_418_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_erase___at___00tst1_spec__3(mut v_00_u03b2_419_: *mut lean_object, mut v_x_420_: *mut lean_object, mut v_t_421_: *mut lean_object) -> *mut lean_object{
let mut v___x_422_: *mut lean_object = core::ptr::null_mut(); 
v___x_422_ = l_Lean_RBNode_erase___at___00tst1_spec__3___redArg(v_x_420_, v_t_421_);
return v___x_422_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_erase___at___00tst1_spec__3___boxed(mut v_00_u03b2_423_: *mut lean_object, mut v_x_424_: *mut lean_object, mut v_t_425_: *mut lean_object) -> *mut lean_object{
let mut v_res_426_: *mut lean_object = core::ptr::null_mut(); 
v_res_426_ = l_Lean_RBNode_erase___at___00tst1_spec__3(v_00_u03b2_423_, v_x_424_, v_t_425_);
lean_dec_ref(v_x_424_);
return v_res_426_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0(mut v_00_u03b2_427_: *mut lean_object, mut v_x_428_: *mut lean_object, mut v_x_429_: *mut lean_object, mut v_x_430_: *mut lean_object) -> *mut lean_object{
let mut v___x_431_: *mut lean_object = core::ptr::null_mut(); 
v___x_431_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst1_spec__0_spec__0___redArg(v_x_428_, v_x_429_, v_x_430_);
return v___x_431_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4(mut v_00_u03b2_432_: *mut lean_object, mut v_x_433_: *mut lean_object, mut v_x_434_: *mut lean_object) -> *mut lean_object{
let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); 
v___x_435_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___redArg(v_x_433_, v_x_434_);
return v___x_435_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4___boxed(mut v_00_u03b2_436_: *mut lean_object, mut v_x_437_: *mut lean_object, mut v_x_438_: *mut lean_object) -> *mut lean_object{
let mut v_res_439_: *mut lean_object = core::ptr::null_mut(); 
v_res_439_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst1_spec__3_spec__4(v_00_u03b2_436_, v_x_437_, v_x_438_);
lean_dec_ref(v_x_437_);
return v_res_439_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg___lam__0(mut v_x_440_: *mut lean_object, mut v_y_441_: *mut lean_object) -> u8{
let mut v___x_442_: u8 = 0; 
v___x_442_ = lean_nat_dec_lt(v_x_440_, v_y_441_);
if v___x_442_ == 0 {
let mut v___x_443_: u8 = 0; 
v___x_443_ = lean_nat_dec_eq(v_x_440_, v_y_441_);
if v___x_443_ == 0 {
let mut v___x_444_: u8 = 0; 
v___x_444_ = 2;
return v___x_444_;
} else {
let mut v___x_445_: u8 = 0; 
v___x_445_ = 1;
return v___x_445_;
}
} else {
let mut v___x_446_: u8 = 0; 
v___x_446_ = 0;
return v___x_446_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg___lam__0___boxed(mut v_x_447_: *mut lean_object, mut v_y_448_: *mut lean_object) -> *mut lean_object{
let mut v_res_449_: u8 = 0; let mut v_r_450_: *mut lean_object = core::ptr::null_mut(); 
v_res_449_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg___lam__0(v_x_447_, v_y_448_);
lean_dec(v_y_448_);
lean_dec(v_x_447_);
v_r_450_ = lean_box((v_res_449_) as usize);
return v_r_450_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg(mut v_x_451_: *mut lean_object, mut v_x_452_: *mut lean_object, mut v_x_453_: *mut lean_object) -> *mut lean_object{
let mut v___x_454_: u8 = 0; let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v_color_456_: u8 = 0; let mut v_lchild_457_: *mut lean_object = core::ptr::null_mut(); let mut v_key_458_: *mut lean_object = core::ptr::null_mut(); let mut v_val_459_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_460_: *mut lean_object = core::ptr::null_mut(); let mut v___x_462_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_463_: u8 = 0; let mut v___x_464_: u8 = 0; let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v___x_467_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_468_: *mut lean_object = core::ptr::null_mut(); let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_471_: *mut lean_object = core::ptr::null_mut(); let mut v___x_472_: *mut lean_object = core::ptr::null_mut(); let mut v___x_474_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_475_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_476_: u8 = 0; let mut v_lchild_477_: *mut lean_object = core::ptr::null_mut(); let mut v_key_478_: *mut lean_object = core::ptr::null_mut(); let mut v_val_479_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_480_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_483_: u8 = 0; let mut v___x_484_: u8 = 0; let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); let mut v_color_486_: u8 = 0; let mut v_lchild_487_: *mut lean_object = core::ptr::null_mut(); let mut v_key_488_: *mut lean_object = core::ptr::null_mut(); let mut v_val_489_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_490_: *mut lean_object = core::ptr::null_mut(); let mut v_a_492_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_493_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_494_: *mut lean_object = core::ptr::null_mut(); let mut v_b_495_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_496_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_497_: *mut lean_object = core::ptr::null_mut(); let mut v_c_498_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_499_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_500_: *mut lean_object = core::ptr::null_mut(); let mut v_d_501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_506_: *mut lean_object = core::ptr::null_mut(); let mut v_color_507_: u8 = 0; let mut v_lchild_508_: *mut lean_object = core::ptr::null_mut(); let mut v_key_509_: *mut lean_object = core::ptr::null_mut(); let mut v_val_510_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_511_: *mut lean_object = core::ptr::null_mut(); let mut v_color_512_: u8 = 0; let mut v_lchild_513_: *mut lean_object = core::ptr::null_mut(); let mut v_key_514_: *mut lean_object = core::ptr::null_mut(); let mut v_val_515_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_516_: *mut lean_object = core::ptr::null_mut(); let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_519_: u8 = 0; let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_522_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_523_: u8 = 0; let mut v_unused_524_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_525_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_526_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_527_: *mut lean_object = core::ptr::null_mut(); let mut v___x_529_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_530_: u8 = 0; let mut v___x_532_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_533_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_534_: u8 = 0; let mut v_unused_535_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_536_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_537_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_538_: *mut lean_object = core::ptr::null_mut(); let mut v_color_539_: u8 = 0; let mut v_lchild_540_: *mut lean_object = core::ptr::null_mut(); let mut v_key_541_: *mut lean_object = core::ptr::null_mut(); let mut v_val_542_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_543_: *mut lean_object = core::ptr::null_mut(); let mut v___x_545_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_546_: u8 = 0; let mut v___x_548_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_549_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_550_: u8 = 0; let mut v_unused_551_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_552_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_553_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_554_: *mut lean_object = core::ptr::null_mut(); let mut v___x_555_: *mut lean_object = core::ptr::null_mut(); let mut v___x_556_: *mut lean_object = core::ptr::null_mut(); let mut v___x_558_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_559_: *mut lean_object = core::ptr::null_mut(); let mut v___x_561_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_562_: *mut lean_object = core::ptr::null_mut(); let mut v___x_563_: *mut lean_object = core::ptr::null_mut(); let mut v_color_564_: u8 = 0; let mut v_lchild_565_: *mut lean_object = core::ptr::null_mut(); let mut v_key_566_: *mut lean_object = core::ptr::null_mut(); let mut v_val_567_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_568_: *mut lean_object = core::ptr::null_mut(); let mut v_a_570_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_571_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_572_: *mut lean_object = core::ptr::null_mut(); let mut v_b_573_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_574_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_575_: *mut lean_object = core::ptr::null_mut(); let mut v_c_576_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_577_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_578_: *mut lean_object = core::ptr::null_mut(); let mut v_d_579_: *mut lean_object = core::ptr::null_mut(); let mut v___x_581_: *mut lean_object = core::ptr::null_mut(); let mut v___x_582_: *mut lean_object = core::ptr::null_mut(); let mut v___x_583_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_584_: *mut lean_object = core::ptr::null_mut(); let mut v_color_585_: u8 = 0; let mut v_lchild_586_: *mut lean_object = core::ptr::null_mut(); let mut v_key_587_: *mut lean_object = core::ptr::null_mut(); let mut v_val_588_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_589_: *mut lean_object = core::ptr::null_mut(); let mut v_color_590_: u8 = 0; let mut v_lchild_591_: *mut lean_object = core::ptr::null_mut(); let mut v_key_592_: *mut lean_object = core::ptr::null_mut(); let mut v_val_593_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_594_: *mut lean_object = core::ptr::null_mut(); let mut v___x_596_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_597_: u8 = 0; let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_600_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_601_: u8 = 0; let mut v_unused_602_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_603_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_604_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_605_: *mut lean_object = core::ptr::null_mut(); let mut v___x_607_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_608_: u8 = 0; let mut v___x_610_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_611_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_612_: u8 = 0; let mut v_unused_613_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_614_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_615_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_616_: *mut lean_object = core::ptr::null_mut(); let mut v_color_617_: u8 = 0; let mut v_lchild_618_: *mut lean_object = core::ptr::null_mut(); let mut v_key_619_: *mut lean_object = core::ptr::null_mut(); let mut v_val_620_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_623_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_624_: u8 = 0; let mut v___x_626_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_627_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_628_: u8 = 0; let mut v_unused_629_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_630_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_631_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_632_: *mut lean_object = core::ptr::null_mut(); let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); let mut v___x_634_: *mut lean_object = core::ptr::null_mut(); let mut v___x_636_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_637_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_638_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_451_) == 0 {
let mut v___x_454_: u8 = 0; let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); 
v___x_454_ = 0;
v___x_455_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_455_, 0, v_x_451_);
lean_ctor_set(v___x_455_, 1, v_x_452_);
lean_ctor_set(v___x_455_, 2, v_x_453_);
lean_ctor_set(v___x_455_, 3, v_x_451_);
lean_ctor_set_uint8(v___x_455_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v___x_454_);
return v___x_455_;
} else {
let mut v_color_456_: u8 = 0; 
v_color_456_ = lean_ctor_get_uint8(v_x_451_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_456_ == 0 {
let mut v_lchild_457_: *mut lean_object = core::ptr::null_mut(); let mut v_key_458_: *mut lean_object = core::ptr::null_mut(); let mut v_val_459_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_460_: *mut lean_object = core::ptr::null_mut(); let mut v___x_462_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_463_: u8 = 0; let mut v_isSharedCheck_476_: u8 = 0; 
v_lchild_457_ = lean_ctor_get(v_x_451_, 0);
v_key_458_ = lean_ctor_get(v_x_451_, 1);
v_val_459_ = lean_ctor_get(v_x_451_, 2);
v_rchild_460_ = lean_ctor_get(v_x_451_, 3);
v_isSharedCheck_476_ = (!lean_is_exclusive(v_x_451_)) as u8;
if v_isSharedCheck_476_ == 0 {
v___x_462_ = v_x_451_;
v_isShared_463_ = v_isSharedCheck_476_;
state = 1; continue;
} else {
lean_inc(v_rchild_460_);
lean_inc(v_val_459_);
lean_inc(v_key_458_);
lean_inc(v_lchild_457_);
lean_dec(v_x_451_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_476_;
state = 1; continue;
}
} else {
let mut v_lchild_477_: *mut lean_object = core::ptr::null_mut(); let mut v_key_478_: *mut lean_object = core::ptr::null_mut(); let mut v_val_479_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_480_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_483_: u8 = 0; let mut v_isSharedCheck_638_: u8 = 0; 
v_lchild_477_ = lean_ctor_get(v_x_451_, 0);
v_key_478_ = lean_ctor_get(v_x_451_, 1);
v_val_479_ = lean_ctor_get(v_x_451_, 2);
v_rchild_480_ = lean_ctor_get(v_x_451_, 3);
v_isSharedCheck_638_ = (!lean_is_exclusive(v_x_451_)) as u8;
if v_isSharedCheck_638_ == 0 {
v___x_482_ = v_x_451_;
v_isShared_483_ = v_isSharedCheck_638_;
state = 5; continue;
} else {
lean_inc(v_rchild_480_);
lean_inc(v_val_479_);
lean_inc(v_key_478_);
lean_inc(v_lchild_477_);
lean_dec(v_x_451_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_638_;
state = 5; continue;
}
}
}
}
1 => {
v___x_464_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg___lam__0(v_x_452_, v_key_458_);
match v___x_464_
{
0 => {
let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v___x_467_: *mut lean_object = core::ptr::null_mut(); 
v___x_465_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg(v_lchild_457_, v_x_452_, v_x_453_);
if v_isShared_463_ == 0 {
lean_ctor_set(v___x_462_, 0, v___x_465_);
v___x_467_ = v___x_462_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_468_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_key_458_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_val_459_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_rchild_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
v___x_467_ = v_reuseFailAlloc_468_;
state = 2; continue;
}
}
1 => {
let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_val_459_);
lean_dec(v_key_458_);
if v_isShared_463_ == 0 {
lean_ctor_set(v___x_462_, 2, v_x_453_);
lean_ctor_set(v___x_462_, 1, v_x_452_);
v___x_470_ = v___x_462_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_471_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_lchild_457_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_x_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_x_453_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_rchild_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
v___x_470_ = v_reuseFailAlloc_471_;
state = 3; continue;
}
}
_ => {
let mut v___x_472_: *mut lean_object = core::ptr::null_mut(); let mut v___x_474_: *mut lean_object = core::ptr::null_mut(); 
v___x_472_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg(v_rchild_460_, v_x_452_, v_x_453_);
if v_isShared_463_ == 0 {
lean_ctor_set(v___x_462_, 3, v___x_472_);
v___x_474_ = v___x_462_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_475_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_lchild_457_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_key_458_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_val_459_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v___x_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_475_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
v___x_474_ = v_reuseFailAlloc_475_;
state = 4; continue;
}
}
}
}
5 => {
v___x_484_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg___lam__0(v_x_452_, v_key_478_);
match v___x_484_
{
0 => {
let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); 
v___x_485_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg(v_lchild_477_, v_x_452_, v_x_453_);
if lean_obj_tag(v___x_485_) == 1 {
let mut v_color_486_: u8 = 0; let mut v_lchild_487_: *mut lean_object = core::ptr::null_mut(); let mut v_key_488_: *mut lean_object = core::ptr::null_mut(); let mut v_val_489_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_490_: *mut lean_object = core::ptr::null_mut(); let mut v_a_492_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_493_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_494_: *mut lean_object = core::ptr::null_mut(); let mut v_b_495_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_496_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_497_: *mut lean_object = core::ptr::null_mut(); let mut v_c_498_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_499_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_500_: *mut lean_object = core::ptr::null_mut(); let mut v_d_501_: *mut lean_object = core::ptr::null_mut(); 
v_color_486_ = lean_ctor_get_uint8(v___x_485_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
v_lchild_487_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_lchild_487_);
v_key_488_ = lean_ctor_get(v___x_485_, 1);
lean_inc(v_key_488_);
v_val_489_ = lean_ctor_get(v___x_485_, 2);
lean_inc(v_val_489_);
v_rchild_490_ = lean_ctor_get(v___x_485_, 3);
lean_inc(v_rchild_490_);
if v_color_486_ == 0 {
if lean_obj_tag(v_lchild_487_) == 1 {
let mut v_color_507_: u8 = 0; 
v_color_507_ = lean_ctor_get_uint8(v_lchild_487_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_507_ == 0 {
let mut v_lchild_508_: *mut lean_object = core::ptr::null_mut(); let mut v_key_509_: *mut lean_object = core::ptr::null_mut(); let mut v_val_510_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_511_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_485_, 4);
v_lchild_508_ = lean_ctor_get(v_lchild_487_, 0);
lean_inc(v_lchild_508_);
v_key_509_ = lean_ctor_get(v_lchild_487_, 1);
lean_inc(v_key_509_);
v_val_510_ = lean_ctor_get(v_lchild_487_, 2);
lean_inc(v_val_510_);
v_rchild_511_ = lean_ctor_get(v_lchild_487_, 3);
lean_inc(v_rchild_511_);
lean_dec_ref_known(v_lchild_487_, 4);
v_a_492_ = v_lchild_508_;
v_kx_493_ = v_key_509_;
v_vx_494_ = v_val_510_;
v_b_495_ = v_rchild_511_;
v_ky_496_ = v_key_488_;
v_vy_497_ = v_val_489_;
v_c_498_ = v_rchild_490_;
v_kz_499_ = v_key_478_;
v_vz_500_ = v_val_479_;
v_d_501_ = v_rchild_480_;
state = 6; continue;
} else {
if lean_obj_tag(v_rchild_490_) == 1 {
let mut v_color_512_: u8 = 0; 
v_color_512_ = lean_ctor_get_uint8(v_rchild_490_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_512_ == 0 {
let mut v_lchild_513_: *mut lean_object = core::ptr::null_mut(); let mut v_key_514_: *mut lean_object = core::ptr::null_mut(); let mut v_val_515_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_516_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_485_, 4);
v_lchild_513_ = lean_ctor_get(v_rchild_490_, 0);
lean_inc(v_lchild_513_);
v_key_514_ = lean_ctor_get(v_rchild_490_, 1);
lean_inc(v_key_514_);
v_val_515_ = lean_ctor_get(v_rchild_490_, 2);
lean_inc(v_val_515_);
v_rchild_516_ = lean_ctor_get(v_rchild_490_, 3);
lean_inc(v_rchild_516_);
lean_dec_ref_known(v_rchild_490_, 4);
v_a_492_ = v_lchild_487_;
v_kx_493_ = v_key_488_;
v_vx_494_ = v_val_489_;
v_b_495_ = v_lchild_513_;
v_ky_496_ = v_key_514_;
v_vy_497_ = v_val_515_;
v_c_498_ = v_rchild_516_;
v_kz_499_ = v_key_478_;
v_vz_500_ = v_val_479_;
v_d_501_ = v_rchild_480_;
state = 6; continue;
} else {
let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_519_: u8 = 0; let mut v_isSharedCheck_523_: u8 = 0; 
lean_dec_ref_known(v_lchild_487_, 4);
lean_dec(v_val_489_);
lean_dec(v_key_488_);
lean_del_object(v___x_482_);
v_isSharedCheck_523_ = (!lean_is_exclusive(v_rchild_490_)) as u8;
if v_isSharedCheck_523_ == 0 {
let mut v_unused_524_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_525_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_526_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_527_: *mut lean_object = core::ptr::null_mut(); 
v_unused_524_ = lean_ctor_get(v_rchild_490_, 3);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_rchild_490_, 2);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_rchild_490_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_rchild_490_, 0);
lean_dec(v_unused_527_);
v___x_518_ = v_rchild_490_;
v_isShared_519_ = v_isSharedCheck_523_;
state = 8; continue;
} else {
lean_dec(v_rchild_490_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
state = 8; continue;
}
}
} else {
let mut v___x_529_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_530_: u8 = 0; let mut v_isSharedCheck_534_: u8 = 0; 
lean_dec(v_rchild_490_);
lean_dec(v_val_489_);
lean_dec(v_key_488_);
lean_del_object(v___x_482_);
v_isSharedCheck_534_ = (!lean_is_exclusive(v_lchild_487_)) as u8;
if v_isSharedCheck_534_ == 0 {
let mut v_unused_535_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_536_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_537_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_538_: *mut lean_object = core::ptr::null_mut(); 
v_unused_535_ = lean_ctor_get(v_lchild_487_, 3);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_lchild_487_, 2);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_lchild_487_, 1);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_lchild_487_, 0);
lean_dec(v_unused_538_);
v___x_529_ = v_lchild_487_;
v_isShared_530_ = v_isSharedCheck_534_;
state = 10; continue;
} else {
lean_dec(v_lchild_487_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
state = 10; continue;
}
}
}
} else {
if lean_obj_tag(v_rchild_490_) == 1 {
let mut v_color_539_: u8 = 0; 
v_color_539_ = lean_ctor_get_uint8(v_rchild_490_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_539_ == 0 {
let mut v_lchild_540_: *mut lean_object = core::ptr::null_mut(); let mut v_key_541_: *mut lean_object = core::ptr::null_mut(); let mut v_val_542_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_543_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_485_, 4);
v_lchild_540_ = lean_ctor_get(v_rchild_490_, 0);
lean_inc(v_lchild_540_);
v_key_541_ = lean_ctor_get(v_rchild_490_, 1);
lean_inc(v_key_541_);
v_val_542_ = lean_ctor_get(v_rchild_490_, 2);
lean_inc(v_val_542_);
v_rchild_543_ = lean_ctor_get(v_rchild_490_, 3);
lean_inc(v_rchild_543_);
lean_dec_ref_known(v_rchild_490_, 4);
v_a_492_ = v_lchild_487_;
v_kx_493_ = v_key_488_;
v_vx_494_ = v_val_489_;
v_b_495_ = v_lchild_540_;
v_ky_496_ = v_key_541_;
v_vy_497_ = v_val_542_;
v_c_498_ = v_rchild_543_;
v_kz_499_ = v_key_478_;
v_vz_500_ = v_val_479_;
v_d_501_ = v_rchild_480_;
state = 6; continue;
} else {
let mut v___x_545_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_546_: u8 = 0; let mut v_isSharedCheck_550_: u8 = 0; 
lean_dec(v_val_489_);
lean_dec(v_key_488_);
lean_dec(v_lchild_487_);
lean_del_object(v___x_482_);
v_isSharedCheck_550_ = (!lean_is_exclusive(v_rchild_490_)) as u8;
if v_isSharedCheck_550_ == 0 {
let mut v_unused_551_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_552_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_553_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_554_: *mut lean_object = core::ptr::null_mut(); 
v_unused_551_ = lean_ctor_get(v_rchild_490_, 3);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_rchild_490_, 2);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_rchild_490_, 1);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_rchild_490_, 0);
lean_dec(v_unused_554_);
v___x_545_ = v_rchild_490_;
v_isShared_546_ = v_isSharedCheck_550_;
state = 12; continue;
} else {
lean_dec(v_rchild_490_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
state = 12; continue;
}
}
} else {
let mut v___x_555_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_490_);
lean_dec(v_val_489_);
lean_dec(v_key_488_);
lean_dec(v_lchild_487_);
lean_del_object(v___x_482_);
v___x_555_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_555_, 0, v___x_485_);
lean_ctor_set(v___x_555_, 1, v_key_478_);
lean_ctor_set(v___x_555_, 2, v_val_479_);
lean_ctor_set(v___x_555_, 3, v_rchild_480_);
lean_ctor_set_uint8(v___x_555_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
return v___x_555_;
}
}
} else {
let mut v___x_556_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_490_);
lean_dec(v_val_489_);
lean_dec(v_key_488_);
lean_dec(v_lchild_487_);
lean_del_object(v___x_482_);
v___x_556_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_556_, 0, v___x_485_);
lean_ctor_set(v___x_556_, 1, v_key_478_);
lean_ctor_set(v___x_556_, 2, v_val_479_);
lean_ctor_set(v___x_556_, 3, v_rchild_480_);
lean_ctor_set_uint8(v___x_556_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
return v___x_556_;
}
} else {
let mut v___x_558_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_483_ == 0 {
lean_ctor_set(v___x_482_, 0, v___x_485_);
v___x_558_ = v___x_482_;
state = 14; continue;
} else {
let mut v_reuseFailAlloc_559_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_key_478_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_val_479_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_rchild_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
v___x_558_ = v_reuseFailAlloc_559_;
state = 14; continue;
}
}
}
1 => {
let mut v___x_561_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_val_479_);
lean_dec(v_key_478_);
if v_isShared_483_ == 0 {
lean_ctor_set(v___x_482_, 2, v_x_453_);
lean_ctor_set(v___x_482_, 1, v_x_452_);
v___x_561_ = v___x_482_;
state = 15; continue;
} else {
let mut v_reuseFailAlloc_562_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_lchild_477_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_x_452_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_x_453_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_rchild_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
v___x_561_ = v_reuseFailAlloc_562_;
state = 15; continue;
}
}
_ => {
let mut v___x_563_: *mut lean_object = core::ptr::null_mut(); 
v___x_563_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg(v_rchild_480_, v_x_452_, v_x_453_);
if lean_obj_tag(v___x_563_) == 1 {
let mut v_color_564_: u8 = 0; let mut v_lchild_565_: *mut lean_object = core::ptr::null_mut(); let mut v_key_566_: *mut lean_object = core::ptr::null_mut(); let mut v_val_567_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_568_: *mut lean_object = core::ptr::null_mut(); let mut v_a_570_: *mut lean_object = core::ptr::null_mut(); let mut v_kx_571_: *mut lean_object = core::ptr::null_mut(); let mut v_vx_572_: *mut lean_object = core::ptr::null_mut(); let mut v_b_573_: *mut lean_object = core::ptr::null_mut(); let mut v_ky_574_: *mut lean_object = core::ptr::null_mut(); let mut v_vy_575_: *mut lean_object = core::ptr::null_mut(); let mut v_c_576_: *mut lean_object = core::ptr::null_mut(); let mut v_kz_577_: *mut lean_object = core::ptr::null_mut(); let mut v_vz_578_: *mut lean_object = core::ptr::null_mut(); let mut v_d_579_: *mut lean_object = core::ptr::null_mut(); 
v_color_564_ = lean_ctor_get_uint8(v___x_563_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
v_lchild_565_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_lchild_565_);
v_key_566_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_key_566_);
v_val_567_ = lean_ctor_get(v___x_563_, 2);
lean_inc(v_val_567_);
v_rchild_568_ = lean_ctor_get(v___x_563_, 3);
lean_inc(v_rchild_568_);
if v_color_564_ == 0 {
if lean_obj_tag(v_lchild_565_) == 1 {
let mut v_color_585_: u8 = 0; 
v_color_585_ = lean_ctor_get_uint8(v_lchild_565_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_585_ == 0 {
let mut v_lchild_586_: *mut lean_object = core::ptr::null_mut(); let mut v_key_587_: *mut lean_object = core::ptr::null_mut(); let mut v_val_588_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_589_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_563_, 4);
v_lchild_586_ = lean_ctor_get(v_lchild_565_, 0);
lean_inc(v_lchild_586_);
v_key_587_ = lean_ctor_get(v_lchild_565_, 1);
lean_inc(v_key_587_);
v_val_588_ = lean_ctor_get(v_lchild_565_, 2);
lean_inc(v_val_588_);
v_rchild_589_ = lean_ctor_get(v_lchild_565_, 3);
lean_inc(v_rchild_589_);
lean_dec_ref_known(v_lchild_565_, 4);
v_a_570_ = v_lchild_477_;
v_kx_571_ = v_key_478_;
v_vx_572_ = v_val_479_;
v_b_573_ = v_lchild_586_;
v_ky_574_ = v_key_587_;
v_vy_575_ = v_val_588_;
v_c_576_ = v_rchild_589_;
v_kz_577_ = v_key_566_;
v_vz_578_ = v_val_567_;
v_d_579_ = v_rchild_568_;
state = 16; continue;
} else {
if lean_obj_tag(v_rchild_568_) == 1 {
let mut v_color_590_: u8 = 0; 
v_color_590_ = lean_ctor_get_uint8(v_rchild_568_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_590_ == 0 {
let mut v_lchild_591_: *mut lean_object = core::ptr::null_mut(); let mut v_key_592_: *mut lean_object = core::ptr::null_mut(); let mut v_val_593_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_594_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_563_, 4);
v_lchild_591_ = lean_ctor_get(v_rchild_568_, 0);
lean_inc(v_lchild_591_);
v_key_592_ = lean_ctor_get(v_rchild_568_, 1);
lean_inc(v_key_592_);
v_val_593_ = lean_ctor_get(v_rchild_568_, 2);
lean_inc(v_val_593_);
v_rchild_594_ = lean_ctor_get(v_rchild_568_, 3);
lean_inc(v_rchild_594_);
lean_dec_ref_known(v_rchild_568_, 4);
v_a_570_ = v_lchild_477_;
v_kx_571_ = v_key_478_;
v_vx_572_ = v_val_479_;
v_b_573_ = v_lchild_565_;
v_ky_574_ = v_key_566_;
v_vy_575_ = v_val_567_;
v_c_576_ = v_lchild_591_;
v_kz_577_ = v_key_592_;
v_vz_578_ = v_val_593_;
v_d_579_ = v_rchild_594_;
state = 16; continue;
} else {
let mut v___x_596_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_597_: u8 = 0; let mut v_isSharedCheck_601_: u8 = 0; 
lean_dec_ref_known(v_lchild_565_, 4);
lean_dec(v_val_567_);
lean_dec(v_key_566_);
lean_del_object(v___x_482_);
v_isSharedCheck_601_ = (!lean_is_exclusive(v_rchild_568_)) as u8;
if v_isSharedCheck_601_ == 0 {
let mut v_unused_602_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_603_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_604_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_605_: *mut lean_object = core::ptr::null_mut(); 
v_unused_602_ = lean_ctor_get(v_rchild_568_, 3);
lean_dec(v_unused_602_);
v_unused_603_ = lean_ctor_get(v_rchild_568_, 2);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_rchild_568_, 1);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_rchild_568_, 0);
lean_dec(v_unused_605_);
v___x_596_ = v_rchild_568_;
v_isShared_597_ = v_isSharedCheck_601_;
state = 18; continue;
} else {
lean_dec(v_rchild_568_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
state = 18; continue;
}
}
} else {
let mut v___x_607_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_608_: u8 = 0; let mut v_isSharedCheck_612_: u8 = 0; 
lean_dec(v_rchild_568_);
lean_dec(v_val_567_);
lean_dec(v_key_566_);
lean_del_object(v___x_482_);
v_isSharedCheck_612_ = (!lean_is_exclusive(v_lchild_565_)) as u8;
if v_isSharedCheck_612_ == 0 {
let mut v_unused_613_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_614_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_615_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_616_: *mut lean_object = core::ptr::null_mut(); 
v_unused_613_ = lean_ctor_get(v_lchild_565_, 3);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_lchild_565_, 2);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_lchild_565_, 1);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_lchild_565_, 0);
lean_dec(v_unused_616_);
v___x_607_ = v_lchild_565_;
v_isShared_608_ = v_isSharedCheck_612_;
state = 20; continue;
} else {
lean_dec(v_lchild_565_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
state = 20; continue;
}
}
}
} else {
if lean_obj_tag(v_rchild_568_) == 1 {
let mut v_color_617_: u8 = 0; 
v_color_617_ = lean_ctor_get_uint8(v_rchild_568_, (core::mem::size_of::<*mut lean_object>()*4) as u32);
if v_color_617_ == 0 {
let mut v_lchild_618_: *mut lean_object = core::ptr::null_mut(); let mut v_key_619_: *mut lean_object = core::ptr::null_mut(); let mut v_val_620_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_621_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_563_, 4);
v_lchild_618_ = lean_ctor_get(v_rchild_568_, 0);
lean_inc(v_lchild_618_);
v_key_619_ = lean_ctor_get(v_rchild_568_, 1);
lean_inc(v_key_619_);
v_val_620_ = lean_ctor_get(v_rchild_568_, 2);
lean_inc(v_val_620_);
v_rchild_621_ = lean_ctor_get(v_rchild_568_, 3);
lean_inc(v_rchild_621_);
lean_dec_ref_known(v_rchild_568_, 4);
v_a_570_ = v_lchild_477_;
v_kx_571_ = v_key_478_;
v_vx_572_ = v_val_479_;
v_b_573_ = v_lchild_565_;
v_ky_574_ = v_key_566_;
v_vy_575_ = v_val_567_;
v_c_576_ = v_lchild_618_;
v_kz_577_ = v_key_619_;
v_vz_578_ = v_val_620_;
v_d_579_ = v_rchild_621_;
state = 16; continue;
} else {
let mut v___x_623_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_624_: u8 = 0; let mut v_isSharedCheck_628_: u8 = 0; 
lean_dec(v_val_567_);
lean_dec(v_key_566_);
lean_dec(v_lchild_565_);
lean_del_object(v___x_482_);
v_isSharedCheck_628_ = (!lean_is_exclusive(v_rchild_568_)) as u8;
if v_isSharedCheck_628_ == 0 {
let mut v_unused_629_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_630_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_631_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_632_: *mut lean_object = core::ptr::null_mut(); 
v_unused_629_ = lean_ctor_get(v_rchild_568_, 3);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_rchild_568_, 2);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_rchild_568_, 1);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_rchild_568_, 0);
lean_dec(v_unused_632_);
v___x_623_ = v_rchild_568_;
v_isShared_624_ = v_isSharedCheck_628_;
state = 22; continue;
} else {
lean_dec(v_rchild_568_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
state = 22; continue;
}
}
} else {
let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_568_);
lean_dec(v_val_567_);
lean_dec(v_key_566_);
lean_dec(v_lchild_565_);
lean_del_object(v___x_482_);
v___x_633_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_633_, 0, v_lchild_477_);
lean_ctor_set(v___x_633_, 1, v_key_478_);
lean_ctor_set(v___x_633_, 2, v_val_479_);
lean_ctor_set(v___x_633_, 3, v___x_563_);
lean_ctor_set_uint8(v___x_633_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
return v___x_633_;
}
}
} else {
let mut v___x_634_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_rchild_568_);
lean_dec(v_val_567_);
lean_dec(v_key_566_);
lean_dec(v_lchild_565_);
lean_del_object(v___x_482_);
v___x_634_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v___x_634_, 0, v_lchild_477_);
lean_ctor_set(v___x_634_, 1, v_key_478_);
lean_ctor_set(v___x_634_, 2, v_val_479_);
lean_ctor_set(v___x_634_, 3, v___x_563_);
lean_ctor_set_uint8(v___x_634_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
return v___x_634_;
}
} else {
let mut v___x_636_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_483_ == 0 {
lean_ctor_set(v___x_482_, 3, v___x_563_);
v___x_636_ = v___x_482_;
state = 24; continue;
} else {
let mut v_reuseFailAlloc_637_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_lchild_477_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_key_478_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_val_479_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v___x_563_);
lean_ctor_set_uint8(v_reuseFailAlloc_637_, (core::mem::size_of::<*mut lean_object>()*4) as u32, v_color_456_);
v___x_636_ = v_reuseFailAlloc_637_;
state = 24; continue;
}
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_insert___at___00tst2_spec__0___redArg(mut v_t_639_: *mut lean_object, mut v_k_640_: *mut lean_object, mut v_v_641_: *mut lean_object) -> *mut lean_object{
let mut v___x_642_: u8 = 0; 
v___x_642_ = l_Lean_RBNode_isRed___redArg(v_t_639_);
if v___x_642_ == 0 {
let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); 
v___x_643_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg(v_t_639_, v_k_640_, v_v_641_);
return v___x_643_;
} else {
let mut v___x_644_: *mut lean_object = core::ptr::null_mut(); let mut v___x_645_: *mut lean_object = core::ptr::null_mut(); 
v___x_644_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg(v_t_639_, v_k_640_, v_v_641_);
v___x_645_ = l_Lean_RBNode_setBlack___redArg(v___x_644_);
return v___x_645_;
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00tst2_spec__1___redArg(mut v_n_646_: *mut lean_object, mut v_j_647_: *mut lean_object, mut v_a_648_: *mut lean_object) -> *mut lean_object{
let mut v_zero_649_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_650_: u8 = 0; let mut v_one_651_: *mut lean_object = core::ptr::null_mut(); let mut v_n_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_656_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_649_ = lean_unsigned_to_nat(0);
v_isZero_650_ = lean_nat_dec_eq(v_j_647_, v_zero_649_);
if v_isZero_650_ == 1 {
lean_dec(v_j_647_);
return v_a_648_;
} else {
let mut v_one_651_: *mut lean_object = core::ptr::null_mut(); let mut v_n_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_656_: *mut lean_object = core::ptr::null_mut(); 
v_one_651_ = lean_unsigned_to_nat(1);
v_n_652_ = lean_nat_sub(v_j_647_, v_one_651_);
v___x_653_ = lean_nat_sub(v_n_646_, v_j_647_);
lean_dec(v_j_647_);
v___x_654_ = lean_unsigned_to_nat(10);
v___x_655_ = lean_nat_mul(v___x_653_, v___x_654_);
v___x_656_ = l_Lean_RBNode_insert___at___00tst2_spec__0___redArg(v_a_648_, v___x_653_, v___x_655_);
v_j_647_ = v_n_652_;
v_a_648_ = v___x_656_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00tst2_spec__1___redArg___boxed(mut v_n_658_: *mut lean_object, mut v_j_659_: *mut lean_object, mut v_a_660_: *mut lean_object) -> *mut lean_object{
let mut v_res_661_: *mut lean_object = core::ptr::null_mut(); 
v_res_661_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00tst2_spec__1___redArg(v_n_658_, v_j_659_, v_a_660_);
lean_dec(v_n_658_);
return v_res_661_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg(mut v_x_662_: *mut lean_object, mut v_x_663_: *mut lean_object) -> *mut lean_object{
let mut v_lchild_664_: *mut lean_object = core::ptr::null_mut(); let mut v_key_665_: *mut lean_object = core::ptr::null_mut(); let mut v_val_666_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_667_: *mut lean_object = core::ptr::null_mut(); let mut v___x_669_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_670_: u8 = 0; let mut v___x_671_: u8 = 0; let mut v___x_672_: u8 = 0; let mut v___x_673_: u8 = 0; let mut v___x_674_: u8 = 0; let mut v___x_675_: *mut lean_object = core::ptr::null_mut(); let mut v___x_677_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_678_: *mut lean_object = core::ptr::null_mut(); let mut v___x_679_: *mut lean_object = core::ptr::null_mut(); let mut v___x_680_: *mut lean_object = core::ptr::null_mut(); let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_682_: u8 = 0; let mut v___x_683_: u8 = 0; let mut v___x_684_: *mut lean_object = core::ptr::null_mut(); let mut v___x_686_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_687_: *mut lean_object = core::ptr::null_mut(); let mut v___x_688_: *mut lean_object = core::ptr::null_mut(); let mut v___x_689_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_690_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_663_) == 0 {
return v_x_663_;
} else {
let mut v_lchild_664_: *mut lean_object = core::ptr::null_mut(); let mut v_key_665_: *mut lean_object = core::ptr::null_mut(); let mut v_val_666_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_667_: *mut lean_object = core::ptr::null_mut(); let mut v___x_669_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_670_: u8 = 0; let mut v_isSharedCheck_690_: u8 = 0; 
v_lchild_664_ = lean_ctor_get(v_x_663_, 0);
v_key_665_ = lean_ctor_get(v_x_663_, 1);
v_val_666_ = lean_ctor_get(v_x_663_, 2);
v_rchild_667_ = lean_ctor_get(v_x_663_, 3);
v_isSharedCheck_690_ = (!lean_is_exclusive(v_x_663_)) as u8;
if v_isSharedCheck_690_ == 0 {
v___x_669_ = v_x_663_;
v_isShared_670_ = v_isSharedCheck_690_;
state = 1; continue;
} else {
lean_inc(v_rchild_667_);
lean_inc(v_val_666_);
lean_inc(v_key_665_);
lean_inc(v_lchild_664_);
lean_dec(v_x_663_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_690_;
state = 1; continue;
}
}
}
1 => {
v___x_671_ = lean_nat_dec_lt(v_x_662_, v_key_665_);
if v___x_671_ == 0 {
let mut v___x_672_: u8 = 0; 
v___x_672_ = lean_nat_dec_eq(v_x_662_, v_key_665_);
if v___x_672_ == 0 {
let mut v___x_673_: u8 = 0; 
v___x_673_ = l_Lean_RBNode_isBlack___redArg(v_rchild_667_);
if v___x_673_ == 0 {
let mut v___x_674_: u8 = 0; let mut v___x_675_: *mut lean_object = core::ptr::null_mut(); let mut v___x_677_: *mut lean_object = core::ptr::null_mut(); 
v___x_674_ = 0;
v___x_675_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg(v_x_662_, v_rchild_667_);
if v_isShared_670_ == 0 {
lean_ctor_set(v___x_669_, 3, v___x_675_);
v___x_677_ = v___x_669_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_678_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_lchild_664_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_key_665_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_val_666_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
state = 2; continue;
}
} else {
let mut v___x_679_: *mut lean_object = core::ptr::null_mut(); let mut v___x_680_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_669_);
v___x_679_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg(v_x_662_, v_rchild_667_);
v___x_680_ = l_Lean_RBNode_balRight___redArg(v_lchild_664_, v_key_665_, v_val_666_, v___x_679_);
return v___x_680_;
}
} else {
let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_669_);
lean_dec(v_val_666_);
lean_dec(v_key_665_);
v___x_681_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_664_, v_rchild_667_);
return v___x_681_;
}
} else {
let mut v___x_682_: u8 = 0; 
v___x_682_ = l_Lean_RBNode_isBlack___redArg(v_lchild_664_);
if v___x_682_ == 0 {
let mut v___x_683_: u8 = 0; let mut v___x_684_: *mut lean_object = core::ptr::null_mut(); let mut v___x_686_: *mut lean_object = core::ptr::null_mut(); 
v___x_683_ = 0;
v___x_684_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg(v_x_662_, v_lchild_664_);
if v_isShared_670_ == 0 {
lean_ctor_set(v___x_669_, 0, v___x_684_);
v___x_686_ = v___x_669_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_687_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 4, (1) as u32);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_key_665_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_val_666_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_rchild_667_);
v___x_686_ = v_reuseFailAlloc_687_;
state = 3; continue;
}
} else {
let mut v___x_688_: *mut lean_object = core::ptr::null_mut(); let mut v___x_689_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_669_);
v___x_688_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg(v_x_662_, v_lchild_664_);
v___x_689_ = l_Lean_RBNode_balLeft___redArg(v___x_688_, v_key_665_, v_val_666_, v_rchild_667_);
return v___x_689_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg___boxed(mut v_x_691_: *mut lean_object, mut v_x_692_: *mut lean_object) -> *mut lean_object{
let mut v_res_693_: *mut lean_object = core::ptr::null_mut(); 
v_res_693_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg(v_x_691_, v_x_692_);
lean_dec(v_x_691_);
return v_res_693_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_erase___at___00tst2_spec__3___redArg(mut v_x_694_: *mut lean_object, mut v_t_695_: *mut lean_object) -> *mut lean_object{
let mut v_t_696_: *mut lean_object = core::ptr::null_mut(); let mut v___x_697_: *mut lean_object = core::ptr::null_mut(); 
v_t_696_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg(v_x_694_, v_t_695_);
v___x_697_ = l_Lean_RBNode_setBlack___redArg(v_t_696_);
return v___x_697_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_erase___at___00tst2_spec__3___redArg___boxed(mut v_x_698_: *mut lean_object, mut v_t_699_: *mut lean_object) -> *mut lean_object{
let mut v_res_700_: *mut lean_object = core::ptr::null_mut(); 
v_res_700_ = l_Lean_RBNode_erase___at___00tst2_spec__3___redArg(v_x_698_, v_t_699_);
lean_dec(v_x_698_);
return v_res_700_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00tst2_spec__4___redArg(mut v_range_701_: *mut lean_object, mut v_b_702_: *mut lean_object, mut v_i_703_: *mut lean_object) -> *mut lean_object{
let mut v_stop_705_: *mut lean_object = core::ptr::null_mut(); let mut v_step_706_: *mut lean_object = core::ptr::null_mut(); let mut v___x_707_: u8 = 0; let mut v___x_708_: *mut lean_object = core::ptr::null_mut(); let mut v___x_709_: *mut lean_object = core::ptr::null_mut(); let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); let mut v___x_711_: *mut lean_object = core::ptr::null_mut(); let mut v___x_712_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_stop_705_ = lean_ctor_get(v_range_701_, 1);
v_step_706_ = lean_ctor_get(v_range_701_, 2);
v___x_707_ = lean_nat_dec_lt(v_i_703_, v_stop_705_);
if v___x_707_ == 0 {
let mut v___x_708_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_703_);
v___x_708_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_708_, 0, v_b_702_);
return v___x_708_;
} else {
let mut v___x_709_: *mut lean_object = core::ptr::null_mut(); let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); let mut v___x_711_: *mut lean_object = core::ptr::null_mut(); let mut v___x_712_: *mut lean_object = core::ptr::null_mut(); 
v___x_709_ = lean_unsigned_to_nat(2);
v___x_710_ = lean_nat_mul(v___x_709_, v_i_703_);
v___x_711_ = l_Lean_RBNode_erase___at___00tst2_spec__3___redArg(v___x_710_, v_b_702_);
lean_dec(v___x_710_);
v___x_712_ = lean_nat_add(v_i_703_, v_step_706_);
lean_dec(v_i_703_);
v_b_702_ = v___x_711_;
v_i_703_ = v___x_712_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00tst2_spec__4___redArg___boxed(mut v_range_714_: *mut lean_object, mut v_b_715_: *mut lean_object, mut v_i_716_: *mut lean_object, mut v___y_717_: *mut lean_object) -> *mut lean_object{
let mut v_res_718_: *mut lean_object = core::ptr::null_mut(); 
v_res_718_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00tst2_spec__4___redArg(v_range_714_, v_b_715_, v_i_716_);
lean_dec_ref(v_range_714_);
return v_res_718_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_all___at___00tst2_spec__2(mut v_x_719_: *mut lean_object) -> u8{
let mut v___x_720_: u8 = 0; let mut v_lchild_721_: *mut lean_object = core::ptr::null_mut(); let mut v_key_722_: *mut lean_object = core::ptr::null_mut(); let mut v_val_723_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_725_: *mut lean_object = core::ptr::null_mut(); let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_727_: u8 = 0; let mut v___x_728_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_719_) == 0 {
let mut v___x_720_: u8 = 0; 
v___x_720_ = 1;
return v___x_720_;
} else {
let mut v_lchild_721_: *mut lean_object = core::ptr::null_mut(); let mut v_key_722_: *mut lean_object = core::ptr::null_mut(); let mut v_val_723_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_725_: *mut lean_object = core::ptr::null_mut(); let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_727_: u8 = 0; 
v_lchild_721_ = lean_ctor_get(v_x_719_, 0);
v_key_722_ = lean_ctor_get(v_x_719_, 1);
v_val_723_ = lean_ctor_get(v_x_719_, 2);
v_rchild_724_ = lean_ctor_get(v_x_719_, 3);
v___x_725_ = lean_unsigned_to_nat(10);
v___x_726_ = lean_nat_mul(v_key_722_, v___x_725_);
v___x_727_ = lean_nat_dec_eq(v_val_723_, v___x_726_);
lean_dec(v___x_726_);
if v___x_727_ == 0 {
return v___x_727_;
} else {
let mut v___x_728_: u8 = 0; 
v___x_728_ = l_Lean_RBNode_all___at___00tst2_spec__2(v_lchild_721_);
if v___x_728_ == 0 {
return v___x_728_;
} else {
v_x_719_ = v_rchild_724_;
state = 0; continue;
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_all___at___00tst2_spec__2___boxed(mut v_x_730_: *mut lean_object) -> *mut lean_object{
let mut v_res_731_: u8 = 0; let mut v_r_732_: *mut lean_object = core::ptr::null_mut(); 
v_res_731_ = l_Lean_RBNode_all___at___00tst2_spec__2(v_x_730_);
lean_dec(v_x_730_);
v_r_732_ = lean_box((v_res_731_) as usize);
return v_r_732_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__0() -> *mut lean_object{
let mut v_m_733_: *mut lean_object = core::ptr::null_mut(); let mut v_n_734_: *mut lean_object = core::ptr::null_mut(); let mut v_m_735_: *mut lean_object = core::ptr::null_mut(); 
v_m_733_ = lean_box(0);
v_n_734_ = lean_unsigned_to_nat(10000);
v_m_735_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00tst2_spec__1___redArg(v_n_734_, v_n_734_, v_m_733_);
return v_m_735_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__1() -> u8{
let mut v_m_736_: *mut lean_object = core::ptr::null_mut(); let mut v___x_737_: u8 = 0; 
v_m_736_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__0), core::ptr::addr_of_mut!(l_tst2___closed__0_once), _init_l_tst2___closed__0);
v___x_737_ = l_Lean_RBNode_all___at___00tst2_spec__2(v_m_736_);
return v___x_737_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__2() -> *mut lean_object{
let mut v_m_738_: *mut lean_object = core::ptr::null_mut(); let mut v___x_739_: *mut lean_object = core::ptr::null_mut(); 
v_m_738_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__0), core::ptr::addr_of_mut!(l_tst2___closed__0_once), _init_l_tst2___closed__0);
v___x_739_ = l_sz___redArg(v_m_738_);
return v___x_739_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__3() -> u8{
let mut v_n_740_: *mut lean_object = core::ptr::null_mut(); let mut v___x_741_: *mut lean_object = core::ptr::null_mut(); let mut v___x_742_: u8 = 0; 
v_n_740_ = lean_unsigned_to_nat(10000);
v___x_741_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__2), core::ptr::addr_of_mut!(l_tst2___closed__2_once), _init_l_tst2___closed__2);
v___x_742_ = lean_nat_dec_eq(v___x_741_, v_n_740_);
return v___x_742_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__5() -> *mut lean_object{
let mut v_m_744_: *mut lean_object = core::ptr::null_mut(); let mut v___x_745_: *mut lean_object = core::ptr::null_mut(); 
v_m_744_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__0), core::ptr::addr_of_mut!(l_tst2___closed__0_once), _init_l_tst2___closed__0);
v___x_745_ = l_depth___redArg(v_m_744_);
return v___x_745_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__6() -> *mut lean_object{
let mut v___x_746_: *mut lean_object = core::ptr::null_mut(); let mut v___x_747_: *mut lean_object = core::ptr::null_mut(); 
v___x_746_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__5), core::ptr::addr_of_mut!(l_tst2___closed__5_once), _init_l_tst2___closed__5);
v___x_747_ = l_Nat_reprFast(v___x_746_);
return v___x_747_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__7() -> *mut lean_object{
let mut v___x_748_: *mut lean_object = core::ptr::null_mut(); let mut v___x_749_: *mut lean_object = core::ptr::null_mut(); let mut v___x_750_: *mut lean_object = core::ptr::null_mut(); 
v___x_748_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__6), core::ptr::addr_of_mut!(l_tst2___closed__6_once), _init_l_tst2___closed__6);
v___x_749_ = l_tst2___closed__4;
v___x_750_ = lean_string_append(v___x_749_, v___x_748_);
return v___x_750_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__9() -> *mut lean_object{
let mut v___x_752_: *mut lean_object = core::ptr::null_mut(); let mut v___x_753_: *mut lean_object = core::ptr::null_mut(); let mut v___x_754_: *mut lean_object = core::ptr::null_mut(); 
v___x_752_ = l_tst2___closed__8;
v___x_753_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__7), core::ptr::addr_of_mut!(l_tst2___closed__7_once), _init_l_tst2___closed__7);
v___x_754_ = lean_string_append(v___x_753_, v___x_752_);
return v___x_754_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__10() -> *mut lean_object{
let mut v___x_755_: *mut lean_object = core::ptr::null_mut(); let mut v___x_756_: *mut lean_object = core::ptr::null_mut(); 
v___x_755_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__2), core::ptr::addr_of_mut!(l_tst2___closed__2_once), _init_l_tst2___closed__2);
v___x_756_ = l_Nat_reprFast(v___x_755_);
return v___x_756_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst2___closed__11() -> *mut lean_object{
let mut v___x_757_: *mut lean_object = core::ptr::null_mut(); let mut v___x_758_: *mut lean_object = core::ptr::null_mut(); let mut v___x_759_: *mut lean_object = core::ptr::null_mut(); 
v___x_757_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__10), core::ptr::addr_of_mut!(l_tst2___closed__10_once), _init_l_tst2___closed__10);
v___x_758_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__9), core::ptr::addr_of_mut!(l_tst2___closed__9_once), _init_l_tst2___closed__9);
v___x_759_ = lean_string_append(v___x_758_, v___x_757_);
return v___x_759_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst2() -> *mut lean_object{
let mut v_m_765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_766_: u8 = 0; let mut v___x_767_: *mut lean_object = core::ptr::null_mut(); let mut v___x_768_: u8 = 0; let mut v___x_769_: *mut lean_object = core::ptr::null_mut(); let mut v___x_770_: *mut lean_object = core::ptr::null_mut(); let mut v___x_771_: *mut lean_object = core::ptr::null_mut(); let mut v___x_772_: *mut lean_object = core::ptr::null_mut(); let mut v___x_773_: *mut lean_object = core::ptr::null_mut(); let mut v___x_774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_775_: *mut lean_object = core::ptr::null_mut(); let mut v___x_776_: *mut lean_object = core::ptr::null_mut(); let mut v___x_777_: *mut lean_object = core::ptr::null_mut(); let mut v_a_778_: *mut lean_object = core::ptr::null_mut(); let mut v___x_779_: u8 = 0; let mut v___x_780_: *mut lean_object = core::ptr::null_mut(); let mut v___x_781_: *mut lean_object = core::ptr::null_mut(); let mut v___x_782_: u8 = 0; let mut v___x_783_: *mut lean_object = core::ptr::null_mut(); let mut v___x_784_: *mut lean_object = core::ptr::null_mut(); let mut v___x_785_: *mut lean_object = core::ptr::null_mut(); let mut v___x_786_: *mut lean_object = core::ptr::null_mut(); let mut v___x_787_: *mut lean_object = core::ptr::null_mut(); let mut v___x_788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_789_: *mut lean_object = core::ptr::null_mut(); let mut v___x_790_: *mut lean_object = core::ptr::null_mut(); let mut v___x_792_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_793_: u8 = 0; let mut v___x_794_: *mut lean_object = core::ptr::null_mut(); let mut v___x_796_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_797_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_798_: u8 = 0; let mut v_unused_799_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_m_765_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__0), core::ptr::addr_of_mut!(l_tst2___closed__0_once), _init_l_tst2___closed__0);
v___x_766_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst2___closed__1), core::ptr::addr_of_mut!(l_tst2___closed__1_once), _init_l_tst2___closed__1);
v___x_767_ = l_check(v___x_766_);
if lean_obj_tag(v___x_767_) == 0 {
let mut v___x_768_: u8 = 0; let mut v___x_769_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_767_, 1);
v___x_768_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst2___closed__3), core::ptr::addr_of_mut!(l_tst2___closed__3_once), _init_l_tst2___closed__3);
v___x_769_ = l_check(v___x_768_);
if lean_obj_tag(v___x_769_) == 0 {
let mut v___x_770_: *mut lean_object = core::ptr::null_mut(); let mut v___x_771_: *mut lean_object = core::ptr::null_mut(); let mut v___x_772_: *mut lean_object = core::ptr::null_mut(); let mut v___x_773_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_769_, 1);
v___x_770_ = l_tst2___closed__4;
v___x_771_ = l_tst2___closed__8;
v___x_772_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst2___closed__11), core::ptr::addr_of_mut!(l_tst2___closed__11_once), _init_l_tst2___closed__11);
v___x_773_ = l_IO_println___at___00check_spec__0(v___x_772_);
if lean_obj_tag(v___x_773_) == 0 {
let mut v___x_774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_775_: *mut lean_object = core::ptr::null_mut(); let mut v___x_776_: *mut lean_object = core::ptr::null_mut(); let mut v___x_777_: *mut lean_object = core::ptr::null_mut(); let mut v_a_778_: *mut lean_object = core::ptr::null_mut(); let mut v___x_779_: u8 = 0; let mut v___x_780_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_773_, 1);
v___x_774_ = lean_unsigned_to_nat(0);
v___x_775_ = lean_unsigned_to_nat(5000);
v___x_776_ = l_tst2___closed__12;
v___x_777_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00tst2_spec__4___redArg(v___x_776_, v_m_765_, v___x_774_);
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref(v___x_777_);
v___x_779_ = l_Lean_RBNode_all___at___00tst2_spec__2(v_a_778_);
v___x_780_ = l_check(v___x_779_);
if lean_obj_tag(v___x_780_) == 0 {
let mut v___x_781_: *mut lean_object = core::ptr::null_mut(); let mut v___x_782_: u8 = 0; let mut v___x_783_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_780_, 1);
v___x_781_ = l_sz___redArg(v_a_778_);
v___x_782_ = lean_nat_dec_eq(v___x_781_, v___x_775_);
v___x_783_ = l_check(v___x_782_);
if lean_obj_tag(v___x_783_) == 0 {
let mut v___x_784_: *mut lean_object = core::ptr::null_mut(); let mut v___x_785_: *mut lean_object = core::ptr::null_mut(); let mut v___x_786_: *mut lean_object = core::ptr::null_mut(); let mut v___x_787_: *mut lean_object = core::ptr::null_mut(); let mut v___x_788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_789_: *mut lean_object = core::ptr::null_mut(); let mut v___x_790_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_783_, 1);
v___x_784_ = l_depth___redArg(v_a_778_);
lean_dec(v_a_778_);
v___x_785_ = l_Nat_reprFast(v___x_784_);
v___x_786_ = lean_string_append(v___x_770_, v___x_785_);
lean_dec_ref(v___x_785_);
v___x_787_ = lean_string_append(v___x_786_, v___x_771_);
v___x_788_ = l_Nat_reprFast(v___x_781_);
v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
lean_dec_ref(v___x_788_);
v___x_790_ = l_IO_println___at___00check_spec__0(v___x_789_);
if lean_obj_tag(v___x_790_) == 0 {
let mut v___x_792_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_793_: u8 = 0; let mut v_isSharedCheck_798_: u8 = 0; 
v_isSharedCheck_798_ = (!lean_is_exclusive(v___x_790_)) as u8;
if v_isSharedCheck_798_ == 0 {
let mut v_unused_799_: *mut lean_object = core::ptr::null_mut(); 
v_unused_799_ = lean_ctor_get(v___x_790_, 0);
lean_dec(v_unused_799_);
v___x_792_ = v___x_790_;
v_isShared_793_ = v_isSharedCheck_798_;
state = 1; continue;
} else {
lean_dec(v___x_790_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_798_;
state = 1; continue;
}
} else {
return v___x_790_;
}
} else {
lean_dec(v___x_781_);
lean_dec(v_a_778_);
return v___x_783_;
}
} else {
lean_dec(v_a_778_);
return v___x_780_;
}
} else {
return v___x_773_;
}
} else {
return v___x_769_;
}
} else {
return v___x_767_;
}
}
1 => {
v___x_794_ = lean_box(0);
if v_isShared_793_ == 0 {
lean_ctor_set(v___x_792_, 0, v___x_794_);
v___x_796_ = v___x_792_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_797_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_tst2___boxed(mut v_a_800_: *mut lean_object) -> *mut lean_object{
let mut v_res_801_: *mut lean_object = core::ptr::null_mut(); 
v_res_801_ = l_tst2();
return v_res_801_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_insert___at___00tst2_spec__0(mut v_00_u03b2_802_: *mut lean_object, mut v_t_803_: *mut lean_object, mut v_k_804_: *mut lean_object, mut v_v_805_: *mut lean_object) -> *mut lean_object{
let mut v___x_806_: *mut lean_object = core::ptr::null_mut(); 
v___x_806_ = l_Lean_RBNode_insert___at___00tst2_spec__0___redArg(v_t_803_, v_k_804_, v_v_805_);
return v___x_806_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00tst2_spec__1(mut v_n_807_: *mut lean_object, mut v_j_808_: *mut lean_object, mut v_a_809_: *mut lean_object, mut v_a_810_: *mut lean_object) -> *mut lean_object{
let mut v___x_811_: *mut lean_object = core::ptr::null_mut(); 
v___x_811_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00tst2_spec__1___redArg(v_n_807_, v_j_808_, v_a_810_);
return v___x_811_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00tst2_spec__1___boxed(mut v_n_812_: *mut lean_object, mut v_j_813_: *mut lean_object, mut v_a_814_: *mut lean_object, mut v_a_815_: *mut lean_object) -> *mut lean_object{
let mut v_res_816_: *mut lean_object = core::ptr::null_mut(); 
v_res_816_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00tst2_spec__1(v_n_812_, v_j_813_, v_a_814_, v_a_815_);
lean_dec(v_n_812_);
return v_res_816_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_erase___at___00tst2_spec__3(mut v_00_u03b2_817_: *mut lean_object, mut v_x_818_: *mut lean_object, mut v_t_819_: *mut lean_object) -> *mut lean_object{
let mut v___x_820_: *mut lean_object = core::ptr::null_mut(); 
v___x_820_ = l_Lean_RBNode_erase___at___00tst2_spec__3___redArg(v_x_818_, v_t_819_);
return v___x_820_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_erase___at___00tst2_spec__3___boxed(mut v_00_u03b2_821_: *mut lean_object, mut v_x_822_: *mut lean_object, mut v_t_823_: *mut lean_object) -> *mut lean_object{
let mut v_res_824_: *mut lean_object = core::ptr::null_mut(); 
v_res_824_ = l_Lean_RBNode_erase___at___00tst2_spec__3(v_00_u03b2_821_, v_x_822_, v_t_823_);
lean_dec(v_x_822_);
return v_res_824_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00tst2_spec__4(mut v_range_825_: *mut lean_object, mut v_b_826_: *mut lean_object, mut v_i_827_: *mut lean_object, mut v_hs_828_: *mut lean_object, mut v_hl_829_: *mut lean_object) -> *mut lean_object{
let mut v___x_831_: *mut lean_object = core::ptr::null_mut(); 
v___x_831_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00tst2_spec__4___redArg(v_range_825_, v_b_826_, v_i_827_);
return v___x_831_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00tst2_spec__4___boxed(mut v_range_832_: *mut lean_object, mut v_b_833_: *mut lean_object, mut v_i_834_: *mut lean_object, mut v_hs_835_: *mut lean_object, mut v_hl_836_: *mut lean_object, mut v___y_837_: *mut lean_object) -> *mut lean_object{
let mut v_res_838_: *mut lean_object = core::ptr::null_mut(); 
v_res_838_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00tst2_spec__4(v_range_832_, v_b_833_, v_i_834_, v_hs_835_, v_hl_836_);
lean_dec_ref(v_range_832_);
return v_res_838_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0(mut v_00_u03b2_839_: *mut lean_object, mut v_x_840_: *mut lean_object, mut v_x_841_: *mut lean_object, mut v_x_842_: *mut lean_object) -> *mut lean_object{
let mut v___x_843_: *mut lean_object = core::ptr::null_mut(); 
v___x_843_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00tst2_spec__0_spec__0___redArg(v_x_840_, v_x_841_, v_x_842_);
return v___x_843_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4(mut v_00_u03b2_844_: *mut lean_object, mut v_x_845_: *mut lean_object, mut v_x_846_: *mut lean_object) -> *mut lean_object{
let mut v___x_847_: *mut lean_object = core::ptr::null_mut(); 
v___x_847_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___redArg(v_x_845_, v_x_846_);
return v___x_847_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4___boxed(mut v_00_u03b2_848_: *mut lean_object, mut v_x_849_: *mut lean_object, mut v_x_850_: *mut lean_object) -> *mut lean_object{
let mut v_res_851_: *mut lean_object = core::ptr::null_mut(); 
v_res_851_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00tst2_spec__3_spec__4(v_00_u03b2_848_, v_x_849_, v_x_850_);
lean_dec(v_x_849_);
return v_res_851_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_find___at___00mkRandMap_spec__0___redArg(mut v_x_852_: *mut lean_object, mut v_x_853_: *mut lean_object) -> *mut lean_object{
let mut v___x_854_: *mut lean_object = core::ptr::null_mut(); let mut v_lchild_855_: *mut lean_object = core::ptr::null_mut(); let mut v_key_856_: *mut lean_object = core::ptr::null_mut(); let mut v_val_857_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_858_: *mut lean_object = core::ptr::null_mut(); let mut v___x_859_: u8 = 0; let mut v___x_860_: u8 = 0; let mut v___x_862_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_852_) == 0 {
let mut v___x_854_: *mut lean_object = core::ptr::null_mut(); 
v___x_854_ = lean_box(0);
return v___x_854_;
} else {
let mut v_lchild_855_: *mut lean_object = core::ptr::null_mut(); let mut v_key_856_: *mut lean_object = core::ptr::null_mut(); let mut v_val_857_: *mut lean_object = core::ptr::null_mut(); let mut v_rchild_858_: *mut lean_object = core::ptr::null_mut(); let mut v___x_859_: u8 = 0; 
v_lchild_855_ = lean_ctor_get(v_x_852_, 0);
v_key_856_ = lean_ctor_get(v_x_852_, 1);
v_val_857_ = lean_ctor_get(v_x_852_, 2);
v_rchild_858_ = lean_ctor_get(v_x_852_, 3);
v___x_859_ = lean_nat_dec_lt(v_x_853_, v_key_856_);
if v___x_859_ == 0 {
let mut v___x_860_: u8 = 0; 
v___x_860_ = lean_nat_dec_eq(v_x_853_, v_key_856_);
if v___x_860_ == 0 {
v_x_852_ = v_rchild_858_;
state = 0; continue;
} else {
let mut v___x_862_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_val_857_);
v___x_862_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_862_, 0, v_val_857_);
return v___x_862_;
}
} else {
v_x_852_ = v_lchild_855_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_find___at___00mkRandMap_spec__0___redArg___boxed(mut v_x_864_: *mut lean_object, mut v_x_865_: *mut lean_object) -> *mut lean_object{
let mut v_res_866_: *mut lean_object = core::ptr::null_mut(); 
v_res_866_ = l_Lean_RBNode_find___at___00mkRandMap_spec__0___redArg(v_x_864_, v_x_865_);
lean_dec(v_x_865_);
lean_dec(v_x_864_);
return v_res_866_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkRandMap(mut v_max_867_: *mut lean_object, mut v_x_868_: *mut lean_object, mut v_x_869_: *mut lean_object, mut v_x_870_: *mut lean_object) -> *mut lean_object{
let mut v_zero_872_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_873_: u8 = 0; let mut v___x_874_: *mut lean_object = core::ptr::null_mut(); let mut v___x_875_: *mut lean_object = core::ptr::null_mut(); let mut v___x_876_: *mut lean_object = core::ptr::null_mut(); let mut v___x_877_: *mut lean_object = core::ptr::null_mut(); let mut v_one_878_: *mut lean_object = core::ptr::null_mut(); let mut v_n_879_: *mut lean_object = core::ptr::null_mut(); let mut v___x_880_: *mut lean_object = core::ptr::null_mut(); let mut v___x_881_: *mut lean_object = core::ptr::null_mut(); let mut v___x_882_: u8 = 0; let mut v___x_884_: *mut lean_object = core::ptr::null_mut(); let mut v___x_885_: *mut lean_object = core::ptr::null_mut(); let mut v___x_886_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_872_ = lean_unsigned_to_nat(0);
v_isZero_873_ = lean_nat_dec_eq(v_x_868_, v_zero_872_);
if v_isZero_873_ == 1 {
let mut v___x_874_: *mut lean_object = core::ptr::null_mut(); let mut v___x_875_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_868_);
v___x_874_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_874_, 0, v_x_869_);
lean_ctor_set(v___x_874_, 1, v_x_870_);
v___x_875_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
} else {
let mut v___x_876_: *mut lean_object = core::ptr::null_mut(); let mut v___x_877_: *mut lean_object = core::ptr::null_mut(); let mut v_one_878_: *mut lean_object = core::ptr::null_mut(); let mut v_n_879_: *mut lean_object = core::ptr::null_mut(); let mut v___x_880_: *mut lean_object = core::ptr::null_mut(); let mut v___x_881_: *mut lean_object = core::ptr::null_mut(); let mut v___x_882_: u8 = 0; 
v___x_876_ = l_IO_rand(v_zero_872_, v_max_867_);
v___x_877_ = l_IO_rand(v_zero_872_, v_max_867_);
v_one_878_ = lean_unsigned_to_nat(1);
v_n_879_ = lean_nat_sub(v_x_868_, v_one_878_);
lean_dec(v_x_868_);
v___x_880_ = l_Lean_RBNode_find___at___00mkRandMap_spec__0___redArg(v_x_869_, v___x_876_);
v___x_881_ = lean_box(0);
v___x_882_ = l_Option_instBEq_beq___at___00tst1_spec__2(v___x_880_, v___x_881_);
lean_dec(v___x_880_);
if v___x_882_ == 0 {
lean_dec(v___x_877_);
lean_dec(v___x_876_);
v_x_868_ = v_n_879_;
state = 0; continue;
} else {
let mut v___x_884_: *mut lean_object = core::ptr::null_mut(); let mut v___x_885_: *mut lean_object = core::ptr::null_mut(); let mut v___x_886_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_877_);
lean_inc(v___x_876_);
v___x_884_ = l_Lean_RBNode_insert___at___00tst2_spec__0___redArg(v_x_869_, v___x_876_, v___x_877_);
v___x_885_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_885_, 0, v___x_876_);
lean_ctor_set(v___x_885_, 1, v___x_877_);
v___x_886_ = lean_array_push(v_x_870_, v___x_885_);
v_x_868_ = v_n_879_;
v_x_869_ = v___x_884_;
v_x_870_ = v___x_886_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mkRandMap___boxed(mut v_max_888_: *mut lean_object, mut v_x_889_: *mut lean_object, mut v_x_890_: *mut lean_object, mut v_x_891_: *mut lean_object, mut v_a_892_: *mut lean_object) -> *mut lean_object{
let mut v_res_893_: *mut lean_object = core::ptr::null_mut(); 
v_res_893_ = l_mkRandMap(v_max_888_, v_x_889_, v_x_890_, v_x_891_);
lean_dec(v_max_888_);
return v_res_893_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_find___at___00mkRandMap_spec__0(mut v_00_u03b2_894_: *mut lean_object, mut v_x_895_: *mut lean_object, mut v_x_896_: *mut lean_object) -> *mut lean_object{
let mut v___x_897_: *mut lean_object = core::ptr::null_mut(); 
v___x_897_ = l_Lean_RBNode_find___at___00mkRandMap_spec__0___redArg(v_x_895_, v_x_896_);
return v___x_897_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_RBNode_find___at___00mkRandMap_spec__0___boxed(mut v_00_u03b2_898_: *mut lean_object, mut v_x_899_: *mut lean_object, mut v_x_900_: *mut lean_object) -> *mut lean_object{
let mut v_res_901_: *mut lean_object = core::ptr::null_mut(); 
v_res_901_ = l_Lean_RBNode_find___at___00mkRandMap_spec__0(v_00_u03b2_898_, v_x_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec(v_x_899_);
return v_res_901_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00tst3_spec__0(mut v_as_902_: *mut lean_object, mut v_sz_903_: usize, mut v_i_904_: usize, mut v_b_905_: *mut lean_object) -> *mut lean_object{
let mut v___x_907_: u8 = 0; let mut v___x_908_: *mut lean_object = core::ptr::null_mut(); let mut v_a_909_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_910_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_911_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_912_: *mut lean_object = core::ptr::null_mut(); let mut v___x_914_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_915_: u8 = 0; let mut v_m_917_: *mut lean_object = core::ptr::null_mut(); let mut v___x_918_: *mut lean_object = core::ptr::null_mut(); let mut v___x_919_: *mut lean_object = core::ptr::null_mut(); let mut v___x_921_: *mut lean_object = core::ptr::null_mut(); let mut v___x_922_: usize = 0; let mut v___x_923_: usize = 0; let mut v_reuseFailAlloc_925_: *mut lean_object = core::ptr::null_mut(); let mut v___x_926_: *mut lean_object = core::ptr::null_mut(); let mut v___x_927_: *mut lean_object = core::ptr::null_mut(); let mut v___x_928_: *mut lean_object = core::ptr::null_mut(); let mut v___x_929_: u8 = 0; let mut v___x_930_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_931_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_907_ = lean_usize_dec_lt(v_i_904_, v_sz_903_);
if v___x_907_ == 0 {
let mut v___x_908_: *mut lean_object = core::ptr::null_mut(); 
v___x_908_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_908_, 0, v_b_905_);
return v___x_908_;
} else {
let mut v_a_909_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_910_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_911_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_912_: *mut lean_object = core::ptr::null_mut(); let mut v___x_914_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_915_: u8 = 0; let mut v_isSharedCheck_931_: u8 = 0; 
v_a_909_ = lean_array_uget_borrowed(v_as_902_, v_i_904_);
v_fst_910_ = lean_ctor_get(v_a_909_, 0);
v_fst_911_ = lean_ctor_get(v_b_905_, 0);
v_snd_912_ = lean_ctor_get(v_b_905_, 1);
v_isSharedCheck_931_ = (!lean_is_exclusive(v_b_905_)) as u8;
if v_isSharedCheck_931_ == 0 {
v___x_914_ = v_b_905_;
v_isShared_915_ = v_isSharedCheck_931_;
state = 1; continue;
} else {
lean_inc(v_snd_912_);
lean_inc(v_fst_911_);
lean_dec(v_b_905_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_931_;
state = 1; continue;
}
}
}
1 => {
v___x_926_ = lean_unsigned_to_nat(0);
v___x_927_ = lean_unsigned_to_nat(2);
v___x_928_ = lean_nat_mod(v_snd_912_, v___x_927_);
v___x_929_ = lean_nat_dec_eq(v___x_928_, v___x_926_);
lean_dec(v___x_928_);
if v___x_929_ == 0 {
v_m_917_ = v_fst_911_;
state = 2; continue;
} else {
let mut v___x_930_: *mut lean_object = core::ptr::null_mut(); 
v___x_930_ = l_Lean_RBNode_erase___at___00tst2_spec__3___redArg(v_fst_910_, v_fst_911_);
v_m_917_ = v___x_930_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00tst3_spec__0___boxed(mut v_as_932_: *mut lean_object, mut v_sz_933_: *mut lean_object, mut v_i_934_: *mut lean_object, mut v_b_935_: *mut lean_object, mut v___y_936_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_937_: usize = 0; let mut v_i_boxed_938_: usize = 0; let mut v_res_939_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_937_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_938_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00tst3_spec__0(v_as_932_, v_sz_boxed_937_, v_i_boxed_938_, v_b_935_);
lean_dec_ref(v_as_932_);
return v_res_939_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00tst3_spec__2(mut v_fst_940_: *mut lean_object, mut v_as_941_: *mut lean_object, mut v_i_942_: usize, mut v_stop_943_: usize) -> u8{
let mut v___x_944_: u8 = 0; let mut v___x_945_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_946_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_947_: *mut lean_object = core::ptr::null_mut(); let mut v___x_948_: u8 = 0; let mut v___x_949_: *mut lean_object = core::ptr::null_mut(); let mut v___x_950_: *mut lean_object = core::ptr::null_mut(); let mut v___x_951_: u8 = 0; let mut v___x_952_: usize = 0; let mut v___x_953_: usize = 0; let mut v___x_955_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_944_ = lean_usize_dec_eq(v_i_942_, v_stop_943_);
if v___x_944_ == 0 {
let mut v___x_945_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_946_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_947_: *mut lean_object = core::ptr::null_mut(); let mut v___x_948_: u8 = 0; let mut v___x_949_: *mut lean_object = core::ptr::null_mut(); let mut v___x_950_: *mut lean_object = core::ptr::null_mut(); let mut v___x_951_: u8 = 0; 
v___x_945_ = lean_array_uget_borrowed(v_as_941_, v_i_942_);
v_fst_946_ = lean_ctor_get(v___x_945_, 0);
v_snd_947_ = lean_ctor_get(v___x_945_, 1);
v___x_948_ = 1;
v___x_949_ = l_Lean_RBNode_find___at___00mkRandMap_spec__0___redArg(v_fst_940_, v_fst_946_);
lean_inc(v_snd_947_);
v___x_950_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_950_, 0, v_snd_947_);
v___x_951_ = l_Option_instBEq_beq___at___00tst1_spec__2(v___x_949_, v___x_950_);
lean_dec_ref_known(v___x_950_, 1);
lean_dec(v___x_949_);
if v___x_951_ == 0 {
return v___x_948_;
} else {
if v___x_944_ == 0 {
let mut v___x_952_: usize = 0; let mut v___x_953_: usize = 0; 
v___x_952_ = 1usize;
v___x_953_ = lean_usize_add(v_i_942_, v___x_952_);
v_i_942_ = v___x_953_;
state = 0; continue;
} else {
return v___x_948_;
}
}
} else {
let mut v___x_955_: u8 = 0; 
v___x_955_ = 0;
return v___x_955_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00tst3_spec__2___boxed(mut v_fst_956_: *mut lean_object, mut v_as_957_: *mut lean_object, mut v_i_958_: *mut lean_object, mut v_stop_959_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_960_: usize = 0; let mut v_stop_boxed_961_: usize = 0; let mut v_res_962_: u8 = 0; let mut v_r_963_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_960_ = lean_unbox_usize(v_i_958_);
lean_dec(v_i_958_);
v_stop_boxed_961_ = lean_unbox_usize(v_stop_959_);
lean_dec(v_stop_959_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00tst3_spec__2(v_fst_956_, v_as_957_, v_i_boxed_960_, v_stop_boxed_961_);
lean_dec_ref(v_as_957_);
lean_dec(v_fst_956_);
v_r_963_ = lean_box((v_res_962_) as usize);
return v_r_963_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00tst3_spec__1(mut v___x_964_: *mut lean_object, mut v_as_965_: *mut lean_object, mut v_sz_966_: usize, mut v_i_967_: usize, mut v_b_968_: *mut lean_object) -> *mut lean_object{
let mut v___x_971_: *mut lean_object = core::ptr::null_mut(); let mut v___x_972_: *mut lean_object = core::ptr::null_mut(); let mut v___x_973_: usize = 0; let mut v___x_974_: usize = 0; let mut v___x_976_: u8 = 0; let mut v___x_977_: *mut lean_object = core::ptr::null_mut(); let mut v_a_978_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_979_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_980_: *mut lean_object = core::ptr::null_mut(); let mut v___x_981_: *mut lean_object = core::ptr::null_mut(); let mut v___x_982_: *mut lean_object = core::ptr::null_mut(); let mut v___x_983_: *mut lean_object = core::ptr::null_mut(); let mut v___x_984_: u8 = 0; let mut v___x_985_: *mut lean_object = core::ptr::null_mut(); let mut v___x_986_: *mut lean_object = core::ptr::null_mut(); let mut v___x_987_: u8 = 0; let mut v___x_988_: *mut lean_object = core::ptr::null_mut(); let mut v_a_989_: *mut lean_object = core::ptr::null_mut(); let mut v___x_991_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_992_: u8 = 0; let mut v___x_994_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_995_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_996_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_976_ = lean_usize_dec_lt(v_i_967_, v_sz_966_);
if v___x_976_ == 0 {
let mut v___x_977_: *mut lean_object = core::ptr::null_mut(); 
v___x_977_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_977_, 0, v_b_968_);
return v___x_977_;
} else {
let mut v_a_978_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_979_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_980_: *mut lean_object = core::ptr::null_mut(); let mut v___x_981_: *mut lean_object = core::ptr::null_mut(); let mut v___x_982_: *mut lean_object = core::ptr::null_mut(); let mut v___x_983_: *mut lean_object = core::ptr::null_mut(); let mut v___x_984_: u8 = 0; 
v_a_978_ = lean_array_uget_borrowed(v_as_965_, v_i_967_);
v_fst_979_ = lean_ctor_get(v_a_978_, 0);
v_snd_980_ = lean_ctor_get(v_a_978_, 1);
v___x_981_ = lean_unsigned_to_nat(2);
v___x_982_ = lean_nat_mod(v_b_968_, v___x_981_);
v___x_983_ = lean_unsigned_to_nat(1);
v___x_984_ = lean_nat_dec_eq(v___x_982_, v___x_983_);
lean_dec(v___x_982_);
if v___x_984_ == 0 {
state = 1; continue;
} else {
let mut v___x_985_: *mut lean_object = core::ptr::null_mut(); let mut v___x_986_: *mut lean_object = core::ptr::null_mut(); let mut v___x_987_: u8 = 0; let mut v___x_988_: *mut lean_object = core::ptr::null_mut(); 
v___x_985_ = l_Lean_RBNode_find___at___00mkRandMap_spec__0___redArg(v___x_964_, v_fst_979_);
lean_inc(v_snd_980_);
v___x_986_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_986_, 0, v_snd_980_);
v___x_987_ = l_Option_instBEq_beq___at___00tst1_spec__2(v___x_985_, v___x_986_);
lean_dec_ref_known(v___x_986_, 1);
lean_dec(v___x_985_);
v___x_988_ = l_check(v___x_987_);
if lean_obj_tag(v___x_988_) == 0 {
lean_dec_ref_known(v___x_988_, 1);
state = 1; continue;
} else {
let mut v_a_989_: *mut lean_object = core::ptr::null_mut(); let mut v___x_991_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_992_: u8 = 0; let mut v_isSharedCheck_996_: u8 = 0; 
lean_dec(v_b_968_);
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_996_ = (!lean_is_exclusive(v___x_988_)) as u8;
if v_isSharedCheck_996_ == 0 {
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_996_;
state = 2; continue;
} else {
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
state = 2; continue;
}
}
}
}
}
1 => {
v___x_971_ = lean_unsigned_to_nat(1);
v___x_972_ = lean_nat_add(v_b_968_, v___x_971_);
lean_dec(v_b_968_);
v___x_973_ = 1usize;
v___x_974_ = lean_usize_add(v_i_967_, v___x_973_);
v_i_967_ = v___x_974_;
v_b_968_ = v___x_972_;
state = 0; continue;
}
2 => {
if v_isShared_992_ == 0 {
v___x_994_ = v___x_991_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_995_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
state = 3; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00tst3_spec__1___boxed(mut v___x_997_: *mut lean_object, mut v_as_998_: *mut lean_object, mut v_sz_999_: *mut lean_object, mut v_i_1000_: *mut lean_object, mut v_b_1001_: *mut lean_object, mut v___y_1002_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_1003_: usize = 0; let mut v_i_boxed_1004_: usize = 0; let mut v_res_1005_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_1003_ = lean_unbox_usize(v_sz_999_);
lean_dec(v_sz_999_);
v_i_boxed_1004_ = lean_unbox_usize(v_i_1000_);
lean_dec(v_i_1000_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00tst3_spec__1(v___x_997_, v_as_998_, v_sz_boxed_1003_, v_i_boxed_1004_, v_b_1001_);
lean_dec_ref(v_as_998_);
lean_dec(v___x_997_);
return v_res_1005_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst3(mut v_seed_1011_: *mut lean_object, mut v_n_1012_: *mut lean_object, mut v_max_1013_: *mut lean_object) -> *mut lean_object{
let mut v___x_1015_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1016_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1017_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1018_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1019_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1020_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1021_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1022_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1024_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1025_: u8 = 0; let mut v___x_1026_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1027_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1028_: u8 = 0; let mut v___x_1029_: *mut lean_object = core::ptr::null_mut(); let mut v___y_1031_: u8 = 0; let mut v___x_1032_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1033_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1034_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1035_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1036_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1038_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_1039_: usize = 0; let mut v___x_1040_: usize = 0; let mut v___x_1041_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1042_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1043_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1044_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1045_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1046_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1047_: u8 = 0; let mut v___x_1048_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1049_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1050_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1051_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1052_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1053_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1054_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1055_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1056_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1057_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1058_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1060_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1061_: u8 = 0; let mut v___x_1062_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1064_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1065_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1066_: u8 = 0; let mut v_unused_1067_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1068_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1070_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1071_: u8 = 0; let mut v___x_1073_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1074_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1075_: u8 = 0; let mut v_a_1076_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1078_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1079_: u8 = 0; let mut v___x_1081_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1082_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1083_: u8 = 0; let mut v_reuseFailAlloc_1084_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1085_: u8 = 0; let mut v___x_1086_: u8 = 0; let mut v___x_1087_: usize = 0; let mut v___x_1088_: usize = 0; let mut v___x_1089_: u8 = 0; let mut v___x_1090_: u8 = 0; let mut v_isSharedCheck_1091_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1015_ = l_IO_setRandSeed(v_seed_1011_);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_unsigned_to_nat(0);
v___x_1018_ = l_tst3___closed__0;
v___x_1019_ = l_mkRandMap(v_max_1013_, v_n_1012_, v___x_1016_, v___x_1018_);
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref(v___x_1019_);
v_fst_1021_ = lean_ctor_get(v_a_1020_, 0);
v_snd_1022_ = lean_ctor_get(v_a_1020_, 1);
v_isSharedCheck_1091_ = (!lean_is_exclusive(v_a_1020_)) as u8;
if v_isSharedCheck_1091_ == 0 {
v___x_1024_ = v_a_1020_;
v_isShared_1025_ = v_isSharedCheck_1091_;
state = 1; continue;
} else {
lean_inc(v_snd_1022_);
lean_inc(v_fst_1021_);
lean_dec(v_a_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1091_;
state = 1; continue;
}
}
1 => {
v___x_1026_ = l_sz___redArg(v_fst_1021_);
v___x_1027_ = lean_array_get_size(v_snd_1022_);
v___x_1028_ = lean_nat_dec_eq(v___x_1026_, v___x_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = l_check(v___x_1028_);
if lean_obj_tag(v___x_1029_) == 0 {
let mut v___y_1031_: u8 = 0; let mut v___x_1085_: u8 = 0; 
lean_dec_ref_known(v___x_1029_, 1);
v___x_1085_ = lean_nat_dec_lt(v___x_1017_, v___x_1027_);
if v___x_1085_ == 0 {
let mut v___x_1086_: u8 = 0; 
v___x_1086_ = 1;
v___y_1031_ = v___x_1086_;
state = 2; continue;
} else {
if v___x_1085_ == 0 {
v___y_1031_ = v___x_1085_;
state = 2; continue;
} else {
let mut v___x_1087_: usize = 0; let mut v___x_1088_: usize = 0; let mut v___x_1089_: u8 = 0; 
v___x_1087_ = 0usize;
v___x_1088_ = lean_usize_of_nat(v___x_1027_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00tst3_spec__2(v_fst_1021_, v_snd_1022_, v___x_1087_, v___x_1088_);
if v___x_1089_ == 0 {
v___y_1031_ = v___x_1085_;
state = 2; continue;
} else {
let mut v___x_1090_: u8 = 0; 
v___x_1090_ = 0;
v___y_1031_ = v___x_1090_;
state = 2; continue;
}
}
}
} else {
lean_del_object(v___x_1024_);
lean_dec(v_snd_1022_);
lean_dec(v_fst_1021_);
return v___x_1029_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_tst3___boxed(mut v_seed_1092_: *mut lean_object, mut v_n_1093_: *mut lean_object, mut v_max_1094_: *mut lean_object, mut v_a_1095_: *mut lean_object) -> *mut lean_object{
let mut v_res_1096_: *mut lean_object = core::ptr::null_mut(); 
v_res_1096_ = l_tst3(v_seed_1092_, v_n_1093_, v_max_1094_);
lean_dec(v_max_1094_);
lean_dec(v_seed_1092_);
return v_res_1096_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v___y_1099_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1118_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1119_: u8 = 0; let mut v___x_1120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1122_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1123_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1124_: u8 = 0; let mut v_unused_1125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1127_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1126_ = l_tst1();
if lean_obj_tag(v___x_1126_) == 0 {
let mut v___x_1127_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1126_, 1);
v___x_1127_ = l_tst2();
v___y_1099_ = v___x_1127_;
state = 1; continue;
} else {
v___y_1099_ = v___x_1126_;
state = 1; continue;
}
}
1 => {
if lean_obj_tag(v___y_1099_) == 0 {
let mut v___x_1100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1103_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___y_1099_, 1);
v___x_1100_ = lean_unsigned_to_nat(1);
v___x_1101_ = lean_unsigned_to_nat(1000);
v___x_1102_ = lean_unsigned_to_nat(20000);
v___x_1103_ = l_tst3(v___x_1100_, v___x_1101_, v___x_1102_);
if lean_obj_tag(v___x_1103_) == 0 {
let mut v___x_1104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1106_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1103_, 1);
v___x_1104_ = lean_unsigned_to_nat(2);
v___x_1105_ = lean_unsigned_to_nat(40000);
v___x_1106_ = l_tst3(v___x_1104_, v___x_1101_, v___x_1105_);
if lean_obj_tag(v___x_1106_) == 0 {
let mut v___x_1107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1110_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1106_, 1);
v___x_1107_ = lean_unsigned_to_nat(3);
v___x_1108_ = lean_unsigned_to_nat(100);
v___x_1109_ = lean_unsigned_to_nat(4000);
v___x_1110_ = l_tst3(v___x_1107_, v___x_1108_, v___x_1109_);
if lean_obj_tag(v___x_1110_) == 0 {
let mut v___x_1111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1114_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1110_, 1);
v___x_1111_ = lean_unsigned_to_nat(4);
v___x_1112_ = lean_unsigned_to_nat(5000);
v___x_1113_ = lean_unsigned_to_nat(100000);
v___x_1114_ = l_tst3(v___x_1111_, v___x_1112_, v___x_1113_);
if lean_obj_tag(v___x_1114_) == 0 {
let mut v___x_1115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1116_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1114_, 1);
v___x_1115_ = lean_unsigned_to_nat(5);
v___x_1116_ = l_tst3(v___x_1115_, v___x_1101_, v___x_1105_);
if lean_obj_tag(v___x_1116_) == 0 {
let mut v___x_1118_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1119_: u8 = 0; let mut v_isSharedCheck_1124_: u8 = 0; 
v_isSharedCheck_1124_ = (!lean_is_exclusive(v___x_1116_)) as u8;
if v_isSharedCheck_1124_ == 0 {
let mut v_unused_1125_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1125_ = lean_ctor_get(v___x_1116_, 0);
lean_dec(v_unused_1125_);
v___x_1118_ = v___x_1116_;
v_isShared_1119_ = v_isSharedCheck_1124_;
state = 2; continue;
} else {
lean_dec(v___x_1116_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1124_;
state = 2; continue;
}
} else {
return v___x_1116_;
}
} else {
return v___x_1114_;
}
} else {
return v___x_1110_;
}
} else {
return v___x_1106_;
}
} else {
return v___x_1103_;
}
} else {
return v___y_1099_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_1128_: *mut lean_object) -> *mut lean_object{
let mut v_res_1129_: *mut lean_object = core::ptr::null_mut(); 
v_res_1129_ = l_main___redArg();
return v_res_1129_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_1130_: *mut lean_object) -> *mut lean_object{
let mut v___x_1132_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_xs_1130_);
v___x_1132_ = l_main___redArg();
return v___x_1132_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_1133_: *mut lean_object, mut v_a_1134_: *mut lean_object) -> *mut lean_object{
let mut v_res_1135_: *mut lean_object = core::ptr::null_mut(); 
v_res_1135_ = _lean_main(v_xs_1133_);
return v_res_1135_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_RBMap(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_rbmap__library(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin);
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
  let res = initialize_rbmap__library(1 /* builtin */);
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
