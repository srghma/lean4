// Lean compiler output
// Module: channel
// Imports: public import Init public meta import Init public import Std.Sync.Channel
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Std_CloseableChannel_Sync_send___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Std_CloseableChannel_Sync_recv___redArg(_: *mut lean_object) -> *mut lean_object;
    fn l_List_get_x21Internal___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_io_as_task(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_io_wait(_: *mut lean_object) -> *mut lean_object;
    fn l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(_: *mut lean_object) -> *mut lean_object;
    fn l_Std_CloseableChannel_new___redArg(_: *mut lean_object) -> *mut lean_object;
    fn lean_io_mono_ms_now() -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_float_of_nat(_: *mut lean_object) -> f64;
    fn l_Float_ofScientific(_: *mut lean_object, _: u8, _: *mut lean_object) -> f64;
    fn lean_float_div(_: f64, _: f64) -> f64;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_float_to_string(_: f64) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_div(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_size(_: *mut lean_object) -> usize;
    fn lean_usize_dec_lt(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn l_Std_CloseableChannel_close___redArg(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__0_value: lean_string_object<44> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 115, 101, 110, 100, 32, 111, 110, 32, 97, 110, 32, 97, 108, 114, 101, 97, 100, 121, 32, 99, 108, 111, 115, 101, 100, 32, 99, 104, 97, 110, 110, 101, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 18 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__0_value) as *mut lean_object] };
static mut l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__2_value: lean_string_object<42> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 99, 108, 111, 115, 101, 32, 97, 110, 32, 97, 108, 114, 101, 97, 100, 121, 32, 99, 108, 111, 115, 101, 100, 32, 99, 104, 97, 110, 110, 101, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__2: *mut lean_object = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__3_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 18 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__2_value) as *mut lean_object] };
static mut l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__3: *mut lean_object = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__3_value) as *mut lean_object;
static mut l_run___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_run___closed__0: f64 = 0.0;
#[no_mangle] pub static l_run___closed__1_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [109, 101, 97, 115, 117, 114, 101, 109, 101, 110, 116, 58, 32, 0]};
static mut l_run___closed__1: *mut lean_object = core::ptr::addr_of!(l_run___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_run___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l_run___closed__2: *mut lean_object = core::ptr::addr_of!(l_run___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_run___closed__3_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 115, 0]};
static mut l_run___closed__3: *mut lean_object = core::ptr::addr_of!(l_run___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 48, 95, 115, 112, 115, 99, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_spsc___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__4_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 48, 95, 109, 112, 115, 99, 0]};
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__5_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 48, 95, 109, 112, 109, 99, 0]};
static mut l_main___closed__5: *mut lean_object = core::ptr::addr_of!(l_main___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__6_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 49, 95, 115, 112, 115, 99, 0]};
static mut l_main___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__7_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__8_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 49, 95, 109, 112, 115, 99, 0]};
static mut l_main___closed__8: *mut lean_object = core::ptr::addr_of!(l_main___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__9_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 49, 95, 109, 112, 109, 99, 0]};
static mut l_main___closed__9: *mut lean_object = core::ptr::addr_of!(l_main___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__10_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 110, 95, 115, 112, 115, 99, 0]};
static mut l_main___closed__10: *mut lean_object = core::ptr::addr_of!(l_main___closed__10_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__11_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 110, 95, 109, 112, 115, 99, 0]};
static mut l_main___closed__11: *mut lean_object = core::ptr::addr_of!(l_main___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__12_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 111, 117, 110, 100, 101, 100, 110, 95, 109, 112, 109, 99, 0]};
static mut l_main___closed__12: *mut lean_object = core::ptr::addr_of!(l_main___closed__12_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__13_value: lean_string_object<13> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [98, 111, 117, 110, 100, 101, 100, 110, 95, 115, 101, 113, 0]};
static mut l_main___closed__13: *mut lean_object = core::ptr::addr_of!(l_main___closed__13_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__14_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_seq___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__14: *mut lean_object = core::ptr::addr_of!(l_main___closed__14_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__15_value: lean_string_object<15> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [117, 110, 98, 111, 117, 110, 100, 101, 100, 95, 115, 112, 115, 99, 0]};
static mut l_main___closed__15: *mut lean_object = core::ptr::addr_of!(l_main___closed__15_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__16_value: lean_string_object<15> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [117, 110, 98, 111, 117, 110, 100, 101, 100, 95, 109, 112, 115, 99, 0]};
static mut l_main___closed__16: *mut lean_object = core::ptr::addr_of!(l_main___closed__16_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__17_value: lean_string_object<15> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [117, 110, 98, 111, 117, 110, 100, 101, 100, 95, 109, 112, 109, 99, 0]};
static mut l_main___closed__17: *mut lean_object = core::ptr::addr_of!(l_main___closed__17_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__18_value: lean_string_object<14> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 98, 111, 117, 110, 100, 101, 100, 95, 115, 101, 113, 0]};
static mut l_main___closed__18: *mut lean_object = core::ptr::addr_of!(l_main___closed__18_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00seq_spec__0___redArg(mut v_upperBound_1_: *mut lean_object, mut v_ch_2_: *mut lean_object, mut v_a_3_: *mut lean_object, mut v_b_4_: *mut lean_object) -> *mut lean_object{
let mut v___x_6_: u8 = 0; let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_6_ = lean_nat_dec_lt(v_a_3_, v_upperBound_1_);
if v___x_6_ == 0 {
let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_3_);
lean_dec_ref(v_ch_2_);
v___x_7_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_7_, 0, v_b_4_);
return v___x_7_;
} else {
let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_ch_2_);
v___x_8_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_2_);
lean_dec(v___x_8_);
v___x_9_ = lean_box(0);
v___x_10_ = lean_unsigned_to_nat(1);
v___x_11_ = lean_nat_add(v_a_3_, v___x_10_);
lean_dec(v_a_3_);
v_a_3_ = v___x_11_;
v_b_4_ = v___x_9_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00seq_spec__0___redArg___boxed(mut v_upperBound_13_: *mut lean_object, mut v_ch_14_: *mut lean_object, mut v_a_15_: *mut lean_object, mut v_b_16_: *mut lean_object, mut v___y_17_: *mut lean_object) -> *mut lean_object{
let mut v_res_18_: *mut lean_object = core::ptr::null_mut(); 
v_res_18_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__0___redArg(v_upperBound_13_, v_ch_14_, v_a_15_, v_b_16_);
lean_dec(v_upperBound_13_);
return v_res_18_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg(mut v_upperBound_25_: *mut lean_object, mut v_ch_26_: *mut lean_object, mut v_a_27_: *mut lean_object, mut v_b_28_: *mut lean_object) -> *mut lean_object{
let mut v___x_30_: u8 = 0; let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v_a_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_40_: u8 = 0; let mut v___x_41_: u8 = 0; let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_49_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_50_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_30_ = lean_nat_dec_lt(v_a_27_, v_upperBound_25_);
if v___x_30_ == 0 {
let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_27_);
lean_dec_ref(v_ch_26_);
v___x_31_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_31_, 0, v_b_28_);
return v___x_31_;
} else {
let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_a_27_);
lean_inc_ref(v_ch_26_);
v___x_32_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_26_, v_a_27_);
if lean_obj_tag(v___x_32_) == 0 {
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_32_, 1);
v___x_33_ = lean_box(0);
v___x_34_ = lean_unsigned_to_nat(1);
v___x_35_ = lean_nat_add(v_a_27_, v___x_34_);
lean_dec(v_a_27_);
v_a_27_ = v___x_35_;
v_b_28_ = v___x_33_;
state = 0; continue;
} else {
let mut v_a_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_40_: u8 = 0; let mut v_isSharedCheck_50_: u8 = 0; 
lean_dec(v_a_27_);
lean_dec_ref(v_ch_26_);
v_a_37_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_50_ = (!lean_is_exclusive(v___x_32_)) as u8;
if v_isSharedCheck_50_ == 0 {
v___x_39_ = v___x_32_;
v_isShared_40_ = v_isSharedCheck_50_;
state = 1; continue;
} else {
lean_inc(v_a_37_);
lean_dec(v___x_32_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_50_;
state = 1; continue;
}
}
}
}
1 => {
v___x_41_ = (lean_unbox(v_a_37_) as u8);
lean_dec(v_a_37_);
if v___x_41_ == 0 {
let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
v___x_42_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__1;
if v_isShared_40_ == 0 {
lean_ctor_set(v___x_39_, 0, v___x_42_);
v___x_44_ = v___x_39_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_45_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_42_);
v___x_44_ = v_reuseFailAlloc_45_;
state = 2; continue;
}
} else {
let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); 
v___x_46_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__3;
if v_isShared_40_ == 0 {
lean_ctor_set(v___x_39_, 0, v___x_46_);
v___x_48_ = v___x_39_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_49_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___boxed(mut v_upperBound_51_: *mut lean_object, mut v_ch_52_: *mut lean_object, mut v_a_53_: *mut lean_object, mut v_b_54_: *mut lean_object, mut v___y_55_: *mut lean_object) -> *mut lean_object{
let mut v_res_56_: *mut lean_object = core::ptr::null_mut(); 
v_res_56_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg(v_upperBound_51_, v_ch_52_, v_a_53_, v_b_54_);
lean_dec(v_upperBound_51_);
return v_res_56_;
}
#[no_mangle] pub unsafe extern "C" fn l_seq(mut v_ch_57_: *mut lean_object, mut v_amount_58_: *mut lean_object) -> *mut lean_object{
let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_66_: u8 = 0; let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_69_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_70_: u8 = 0; let mut v_unused_71_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_60_ = lean_unsigned_to_nat(0);
v___x_61_ = lean_box(0);
lean_inc_ref(v_ch_57_);
v___x_62_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg(v_amount_58_, v_ch_57_, v___x_60_, v___x_61_);
if lean_obj_tag(v___x_62_) == 0 {
let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_62_, 1);
v___x_63_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__0___redArg(v_amount_58_, v_ch_57_, v___x_60_, v___x_61_);
if lean_obj_tag(v___x_63_) == 0 {
let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_66_: u8 = 0; let mut v_isSharedCheck_70_: u8 = 0; 
v_isSharedCheck_70_ = (!lean_is_exclusive(v___x_63_)) as u8;
if v_isSharedCheck_70_ == 0 {
let mut v_unused_71_: *mut lean_object = core::ptr::null_mut(); 
v_unused_71_ = lean_ctor_get(v___x_63_, 0);
lean_dec(v_unused_71_);
v___x_65_ = v___x_63_;
v_isShared_66_ = v_isSharedCheck_70_;
state = 1; continue;
} else {
lean_dec(v___x_63_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
state = 1; continue;
}
} else {
return v___x_63_;
}
} else {
lean_dec_ref(v_ch_57_);
return v___x_62_;
}
}
1 => {
if v_isShared_66_ == 0 {
lean_ctor_set(v___x_65_, 0, v___x_61_);
v___x_68_ = v___x_65_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_69_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_61_);
v___x_68_ = v_reuseFailAlloc_69_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_seq___boxed(mut v_ch_72_: *mut lean_object, mut v_amount_73_: *mut lean_object, mut v_a_74_: *mut lean_object) -> *mut lean_object{
let mut v_res_75_: *mut lean_object = core::ptr::null_mut(); 
v_res_75_ = l_seq(v_ch_72_, v_amount_73_);
lean_dec(v_amount_73_);
return v_res_75_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00seq_spec__0(mut v_upperBound_76_: *mut lean_object, mut v_ch_77_: *mut lean_object, mut v_inst_78_: *mut lean_object, mut v_R_79_: *mut lean_object, mut v_a_80_: *mut lean_object, mut v_b_81_: *mut lean_object, mut v_c_82_: *mut lean_object) -> *mut lean_object{
let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); 
v___x_84_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__0___redArg(v_upperBound_76_, v_ch_77_, v_a_80_, v_b_81_);
return v___x_84_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00seq_spec__0___boxed(mut v_upperBound_85_: *mut lean_object, mut v_ch_86_: *mut lean_object, mut v_inst_87_: *mut lean_object, mut v_R_88_: *mut lean_object, mut v_a_89_: *mut lean_object, mut v_b_90_: *mut lean_object, mut v_c_91_: *mut lean_object, mut v___y_92_: *mut lean_object) -> *mut lean_object{
let mut v_res_93_: *mut lean_object = core::ptr::null_mut(); 
v_res_93_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__0(v_upperBound_85_, v_ch_86_, v_inst_87_, v_R_88_, v_a_89_, v_b_90_, v_c_91_);
lean_dec(v_upperBound_85_);
return v_res_93_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00seq_spec__1(mut v_upperBound_94_: *mut lean_object, mut v_ch_95_: *mut lean_object, mut v_inst_96_: *mut lean_object, mut v_R_97_: *mut lean_object, mut v_a_98_: *mut lean_object, mut v_b_99_: *mut lean_object, mut v_c_100_: *mut lean_object) -> *mut lean_object{
let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
v___x_102_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg(v_upperBound_94_, v_ch_95_, v_a_98_, v_b_99_);
return v___x_102_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___boxed(mut v_upperBound_103_: *mut lean_object, mut v_ch_104_: *mut lean_object, mut v_inst_105_: *mut lean_object, mut v_R_106_: *mut lean_object, mut v_a_107_: *mut lean_object, mut v_b_108_: *mut lean_object, mut v_c_109_: *mut lean_object, mut v___y_110_: *mut lean_object) -> *mut lean_object{
let mut v_res_111_: *mut lean_object = core::ptr::null_mut(); 
v_res_111_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1(v_upperBound_103_, v_ch_104_, v_inst_105_, v_R_106_, v_a_107_, v_b_108_, v_c_109_);
lean_dec(v_upperBound_103_);
return v_res_111_;
}
#[no_mangle] pub unsafe extern "C" fn l_spsc___lam__0(mut v_amount_112_: *mut lean_object, mut v_ch_113_: *mut lean_object, mut v___x_114_: *mut lean_object) -> *mut lean_object{
let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_120_: u8 = 0; let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_123_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_124_: u8 = 0; let mut v_unused_125_: *mut lean_object = core::ptr::null_mut(); let mut v_a_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_129_: u8 = 0; let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_132_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_133_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_116_ = lean_unsigned_to_nat(0);
v___x_117_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg(v_amount_112_, v_ch_113_, v___x_116_, v___x_114_);
if lean_obj_tag(v___x_117_) == 0 {
let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_120_: u8 = 0; let mut v_isSharedCheck_124_: u8 = 0; 
v_isSharedCheck_124_ = (!lean_is_exclusive(v___x_117_)) as u8;
if v_isSharedCheck_124_ == 0 {
let mut v_unused_125_: *mut lean_object = core::ptr::null_mut(); 
v_unused_125_ = lean_ctor_get(v___x_117_, 0);
lean_dec(v_unused_125_);
v___x_119_ = v___x_117_;
v_isShared_120_ = v_isSharedCheck_124_;
state = 1; continue;
} else {
lean_dec(v___x_117_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
state = 1; continue;
}
} else {
let mut v_a_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_129_: u8 = 0; let mut v_isSharedCheck_133_: u8 = 0; 
v_a_126_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_133_ = (!lean_is_exclusive(v___x_117_)) as u8;
if v_isSharedCheck_133_ == 0 {
v___x_128_ = v___x_117_;
v_isShared_129_ = v_isSharedCheck_133_;
state = 3; continue;
} else {
lean_inc(v_a_126_);
lean_dec(v___x_117_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_120_ == 0 {
lean_ctor_set_tag(v___x_119_, 1);
lean_ctor_set(v___x_119_, 0, v___x_114_);
v___x_122_ = v___x_119_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_123_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_114_);
v___x_122_ = v_reuseFailAlloc_123_;
state = 2; continue;
}
}
3 => {
if v_isShared_129_ == 0 {
lean_ctor_set_tag(v___x_128_, 0);
v___x_131_ = v___x_128_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_132_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_spsc___lam__0___boxed(mut v_amount_134_: *mut lean_object, mut v_ch_135_: *mut lean_object, mut v___x_136_: *mut lean_object, mut v___y_137_: *mut lean_object) -> *mut lean_object{
let mut v_res_138_: *mut lean_object = core::ptr::null_mut(); 
v_res_138_ = l_spsc___lam__0(v_amount_134_, v_ch_135_, v___x_136_);
lean_dec(v_amount_134_);
return v_res_138_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00spsc_spec__0___redArg(mut v_upperBound_139_: *mut lean_object, mut v_ch_140_: *mut lean_object, mut v_a_141_: *mut lean_object, mut v_b_142_: *mut lean_object) -> *mut lean_object{
let mut v___x_144_: u8 = 0; let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_144_ = lean_nat_dec_lt(v_a_141_, v_upperBound_139_);
if v___x_144_ == 0 {
lean_dec(v_a_141_);
lean_dec_ref(v_ch_140_);
return v_b_142_;
} else {
let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_ch_140_);
v___x_145_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_140_);
lean_dec(v___x_145_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_unsigned_to_nat(1);
v___x_148_ = lean_nat_add(v_a_141_, v___x_147_);
lean_dec(v_a_141_);
v_a_141_ = v___x_148_;
v_b_142_ = v___x_146_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00spsc_spec__0___redArg___boxed(mut v_upperBound_150_: *mut lean_object, mut v_ch_151_: *mut lean_object, mut v_a_152_: *mut lean_object, mut v_b_153_: *mut lean_object, mut v___y_154_: *mut lean_object) -> *mut lean_object{
let mut v_res_155_: *mut lean_object = core::ptr::null_mut(); 
v_res_155_ = l_WellFounded_opaqueFix_u2083___at___00spsc_spec__0___redArg(v_upperBound_150_, v_ch_151_, v_a_152_, v_b_153_);
lean_dec(v_upperBound_150_);
return v_res_155_;
}
#[no_mangle] pub unsafe extern "C" fn l_spsc___lam__1(mut v_amount_156_: *mut lean_object, mut v_ch_157_: *mut lean_object, mut v___x_158_: *mut lean_object) -> *mut lean_object{
let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); 
v___x_160_ = lean_unsigned_to_nat(0);
v___x_161_ = l_WellFounded_opaqueFix_u2083___at___00spsc_spec__0___redArg(v_amount_156_, v_ch_157_, v___x_160_, v___x_158_);
return v___x_158_;
}
#[no_mangle] pub unsafe extern "C" fn l_spsc___lam__1___boxed(mut v_amount_162_: *mut lean_object, mut v_ch_163_: *mut lean_object, mut v___x_164_: *mut lean_object, mut v___y_165_: *mut lean_object) -> *mut lean_object{
let mut v_res_166_: *mut lean_object = core::ptr::null_mut(); 
v_res_166_ = l_spsc___lam__1(v_amount_162_, v_ch_163_, v___x_164_);
lean_dec(v_amount_162_);
return v_res_166_;
}
#[no_mangle] pub unsafe extern "C" fn l_spsc(mut v_ch_167_: *mut lean_object, mut v_amount_168_: *mut lean_object) -> *mut lean_object{
let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); let mut v___f_171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_172_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: *mut lean_object = core::ptr::null_mut(); let mut v___f_174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_180_: u8 = 0; let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v___x_183_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_184_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_185_: u8 = 0; let mut v_unused_186_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_170_ = lean_box(0);
lean_inc_ref(v_ch_167_);
lean_inc(v_amount_168_);
v___f_171_ = lean_alloc_closure(l_spsc___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_171_, 0, v_amount_168_);
lean_closure_set(v___f_171_, 1, v_ch_167_);
lean_closure_set(v___f_171_, 2, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(9);
v___x_173_ = lean_io_as_task(v___f_171_, v___x_172_);
v___f_174_ = lean_alloc_closure(l_spsc___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_174_, 0, v_amount_168_);
lean_closure_set(v___f_174_, 1, v_ch_167_);
lean_closure_set(v___f_174_, 2, v___x_170_);
v___x_175_ = lean_io_as_task(v___f_174_, v___x_172_);
v___x_176_ = lean_io_wait(v___x_173_);
v___x_177_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v___x_176_);
if lean_obj_tag(v___x_177_) == 0 {
let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_180_: u8 = 0; let mut v_isSharedCheck_185_: u8 = 0; 
v_isSharedCheck_185_ = (!lean_is_exclusive(v___x_177_)) as u8;
if v_isSharedCheck_185_ == 0 {
let mut v_unused_186_: *mut lean_object = core::ptr::null_mut(); 
v_unused_186_ = lean_ctor_get(v___x_177_, 0);
lean_dec(v_unused_186_);
v___x_179_ = v___x_177_;
v_isShared_180_ = v_isSharedCheck_185_;
state = 1; continue;
} else {
lean_dec(v___x_177_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
state = 1; continue;
}
} else {
lean_dec_ref(v___x_175_);
return v___x_177_;
}
}
1 => {
v___x_181_ = lean_io_wait(v___x_175_);
if v_isShared_180_ == 0 {
lean_ctor_set(v___x_179_, 0, v___x_181_);
v___x_183_ = v___x_179_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_184_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_spsc___boxed(mut v_ch_187_: *mut lean_object, mut v_amount_188_: *mut lean_object, mut v_a_189_: *mut lean_object) -> *mut lean_object{
let mut v_res_190_: *mut lean_object = core::ptr::null_mut(); 
v_res_190_ = l_spsc(v_ch_187_, v_amount_188_);
return v_res_190_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00spsc_spec__0(mut v_upperBound_191_: *mut lean_object, mut v_ch_192_: *mut lean_object, mut v_inst_193_: *mut lean_object, mut v_R_194_: *mut lean_object, mut v_a_195_: *mut lean_object, mut v_b_196_: *mut lean_object, mut v_c_197_: *mut lean_object) -> *mut lean_object{
let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); 
v___x_199_ = l_WellFounded_opaqueFix_u2083___at___00spsc_spec__0___redArg(v_upperBound_191_, v_ch_192_, v_a_195_, v_b_196_);
return v___x_199_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00spsc_spec__0___boxed(mut v_upperBound_200_: *mut lean_object, mut v_ch_201_: *mut lean_object, mut v_inst_202_: *mut lean_object, mut v_R_203_: *mut lean_object, mut v_a_204_: *mut lean_object, mut v_b_205_: *mut lean_object, mut v_c_206_: *mut lean_object, mut v___y_207_: *mut lean_object) -> *mut lean_object{
let mut v_res_208_: *mut lean_object = core::ptr::null_mut(); 
v_res_208_ = l_WellFounded_opaqueFix_u2083___at___00spsc_spec__0(v_upperBound_200_, v_ch_201_, v_inst_202_, v_R_203_, v_a_204_, v_b_205_, v_c_206_);
lean_dec(v_upperBound_200_);
return v_res_208_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mpsc_spec__0(mut v_as_209_: *mut lean_object, mut v_sz_210_: usize, mut v_i_211_: usize, mut v_b_212_: *mut lean_object) -> *mut lean_object{
let mut v___x_214_: u8 = 0; let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v_a_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: usize = 0; let mut v___x_221_: usize = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_214_ = lean_usize_dec_lt(v_i_211_, v_sz_210_);
if v___x_214_ == 0 {
let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); 
v___x_215_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_215_, 0, v_b_212_);
return v___x_215_;
} else {
let mut v_a_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); 
v_a_216_ = lean_array_uget_borrowed(v_as_209_, v_i_211_);
lean_inc(v_a_216_);
v___x_217_ = lean_io_wait(v_a_216_);
v___x_218_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v___x_217_);
if lean_obj_tag(v___x_218_) == 0 {
let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: usize = 0; let mut v___x_221_: usize = 0; 
lean_dec_ref_known(v___x_218_, 1);
v___x_219_ = lean_box(0);
v___x_220_ = 1usize;
v___x_221_ = lean_usize_add(v_i_211_, v___x_220_);
v_i_211_ = v___x_221_;
v_b_212_ = v___x_219_;
state = 0; continue;
} else {
return v___x_218_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mpsc_spec__0___boxed(mut v_as_223_: *mut lean_object, mut v_sz_224_: *mut lean_object, mut v_i_225_: *mut lean_object, mut v_b_226_: *mut lean_object, mut v___y_227_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_228_: usize = 0; let mut v_i_boxed_229_: usize = 0; let mut v_res_230_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_228_ = lean_unbox_usize(v_sz_224_);
lean_dec(v_sz_224_);
v_i_boxed_229_ = lean_unbox_usize(v_i_225_);
lean_dec(v_i_225_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mpsc_spec__0(v_as_223_, v_sz_boxed_228_, v_i_boxed_229_, v_b_226_);
lean_dec_ref(v_as_223_);
return v_res_230_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg___lam__0(mut v___x_231_: *mut lean_object, mut v_ch_232_: *mut lean_object, mut v___x_233_: *mut lean_object) -> *mut lean_object{
let mut v___x_235_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_239_: u8 = 0; let mut v___x_241_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_242_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_243_: u8 = 0; let mut v_unused_244_: *mut lean_object = core::ptr::null_mut(); let mut v_a_245_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_248_: u8 = 0; let mut v___x_250_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_252_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_235_ = lean_unsigned_to_nat(0);
v___x_236_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg(v___x_231_, v_ch_232_, v___x_235_, v___x_233_);
if lean_obj_tag(v___x_236_) == 0 {
let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_239_: u8 = 0; let mut v_isSharedCheck_243_: u8 = 0; 
v_isSharedCheck_243_ = (!lean_is_exclusive(v___x_236_)) as u8;
if v_isSharedCheck_243_ == 0 {
let mut v_unused_244_: *mut lean_object = core::ptr::null_mut(); 
v_unused_244_ = lean_ctor_get(v___x_236_, 0);
lean_dec(v_unused_244_);
v___x_238_ = v___x_236_;
v_isShared_239_ = v_isSharedCheck_243_;
state = 1; continue;
} else {
lean_dec(v___x_236_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
state = 1; continue;
}
} else {
let mut v_a_245_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_248_: u8 = 0; let mut v_isSharedCheck_252_: u8 = 0; 
v_a_245_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_252_ = (!lean_is_exclusive(v___x_236_)) as u8;
if v_isSharedCheck_252_ == 0 {
v___x_247_ = v___x_236_;
v_isShared_248_ = v_isSharedCheck_252_;
state = 3; continue;
} else {
lean_inc(v_a_245_);
lean_dec(v___x_236_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_239_ == 0 {
lean_ctor_set_tag(v___x_238_, 1);
lean_ctor_set(v___x_238_, 0, v___x_233_);
v___x_241_ = v___x_238_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_242_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_233_);
v___x_241_ = v_reuseFailAlloc_242_;
state = 2; continue;
}
}
3 => {
if v_isShared_248_ == 0 {
lean_ctor_set_tag(v___x_247_, 0);
v___x_250_ = v___x_247_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_251_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg___lam__0___boxed(mut v___x_253_: *mut lean_object, mut v_ch_254_: *mut lean_object, mut v___x_255_: *mut lean_object, mut v___y_256_: *mut lean_object) -> *mut lean_object{
let mut v_res_257_: *mut lean_object = core::ptr::null_mut(); 
v_res_257_ = l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg___lam__0(v___x_253_, v_ch_254_, v___x_255_);
lean_dec(v___x_253_);
return v_res_257_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg(mut v_upperBound_258_: *mut lean_object, mut v_amount_259_: *mut lean_object, mut v_threads_260_: *mut lean_object, mut v_ch_261_: *mut lean_object, mut v_a_262_: *mut lean_object, mut v_b_263_: *mut lean_object) -> *mut lean_object{
let mut v___x_265_: u8 = 0; let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); let mut v___f_269_: *mut lean_object = core::ptr::null_mut(); let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_265_ = lean_nat_dec_lt(v_a_262_, v_upperBound_258_);
if v___x_265_ == 0 {
let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_262_);
lean_dec_ref(v_ch_261_);
v___x_266_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_266_, 0, v_b_263_);
return v___x_266_;
} else {
let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); let mut v___f_269_: *mut lean_object = core::ptr::null_mut(); let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); 
v___x_267_ = lean_nat_div(v_amount_259_, v_threads_260_);
v___x_268_ = lean_box(0);
lean_inc_ref(v_ch_261_);
v___f_269_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_269_, 0, v___x_267_);
lean_closure_set(v___f_269_, 1, v_ch_261_);
lean_closure_set(v___f_269_, 2, v___x_268_);
v___x_270_ = lean_unsigned_to_nat(9);
v___x_271_ = lean_io_as_task(v___f_269_, v___x_270_);
v___x_272_ = lean_array_push(v_b_263_, v___x_271_);
v___x_273_ = lean_unsigned_to_nat(1);
v___x_274_ = lean_nat_add(v_a_262_, v___x_273_);
lean_dec(v_a_262_);
v_a_262_ = v___x_274_;
v_b_263_ = v___x_272_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg___boxed(mut v_upperBound_276_: *mut lean_object, mut v_amount_277_: *mut lean_object, mut v_threads_278_: *mut lean_object, mut v_ch_279_: *mut lean_object, mut v_a_280_: *mut lean_object, mut v_b_281_: *mut lean_object, mut v___y_282_: *mut lean_object) -> *mut lean_object{
let mut v_res_283_: *mut lean_object = core::ptr::null_mut(); 
v_res_283_ = l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg(v_upperBound_276_, v_amount_277_, v_threads_278_, v_ch_279_, v_a_280_, v_b_281_);
lean_dec(v_threads_278_);
lean_dec(v_amount_277_);
lean_dec(v_upperBound_276_);
return v_res_283_;
}
#[no_mangle] pub unsafe extern "C" fn l_mpsc(mut v_threads_284_: *mut lean_object, mut v_ch_285_: *mut lean_object, mut v_amount_286_: *mut lean_object) -> *mut lean_object{
let mut v_producers_288_: *mut lean_object = core::ptr::null_mut(); let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v_a_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___f_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); let mut v___x_295_: *mut lean_object = core::ptr::null_mut(); let mut v___x_296_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_297_: usize = 0; let mut v___x_298_: usize = 0; let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_302_: u8 = 0; let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_305_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_306_: u8 = 0; let mut v_unused_307_: *mut lean_object = core::ptr::null_mut(); let mut v_a_308_: *mut lean_object = core::ptr::null_mut(); let mut v___x_310_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_311_: u8 = 0; let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_314_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_315_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_producers_288_ = lean_mk_empty_array_with_capacity(v_threads_284_);
v___x_289_ = lean_unsigned_to_nat(0);
lean_inc_ref(v_ch_285_);
v___x_290_ = l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg(v_threads_284_, v_amount_286_, v_threads_284_, v_ch_285_, v___x_289_, v_producers_288_);
if lean_obj_tag(v___x_290_) == 0 {
let mut v_a_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___f_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); let mut v___x_295_: *mut lean_object = core::ptr::null_mut(); let mut v___x_296_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_297_: usize = 0; let mut v___x_298_: usize = 0; let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = lean_box(0);
v___f_293_ = lean_alloc_closure(l_spsc___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_293_, 0, v_amount_286_);
lean_closure_set(v___f_293_, 1, v_ch_285_);
lean_closure_set(v___f_293_, 2, v___x_292_);
v___x_294_ = lean_unsigned_to_nat(9);
v___x_295_ = lean_io_as_task(v___f_293_, v___x_294_);
v___x_296_ = lean_io_wait(v___x_295_);
lean_dec(v___x_296_);
v_sz_297_ = lean_array_size(v_a_291_);
v___x_298_ = 0usize;
v___x_299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mpsc_spec__0(v_a_291_, v_sz_297_, v___x_298_, v___x_292_);
lean_dec(v_a_291_);
if lean_obj_tag(v___x_299_) == 0 {
let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_302_: u8 = 0; let mut v_isSharedCheck_306_: u8 = 0; 
v_isSharedCheck_306_ = (!lean_is_exclusive(v___x_299_)) as u8;
if v_isSharedCheck_306_ == 0 {
let mut v_unused_307_: *mut lean_object = core::ptr::null_mut(); 
v_unused_307_ = lean_ctor_get(v___x_299_, 0);
lean_dec(v_unused_307_);
v___x_301_ = v___x_299_;
v_isShared_302_ = v_isSharedCheck_306_;
state = 1; continue;
} else {
lean_dec(v___x_299_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
state = 1; continue;
}
} else {
return v___x_299_;
}
} else {
let mut v_a_308_: *mut lean_object = core::ptr::null_mut(); let mut v___x_310_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_311_: u8 = 0; let mut v_isSharedCheck_315_: u8 = 0; 
lean_dec(v_amount_286_);
lean_dec_ref(v_ch_285_);
v_a_308_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_315_ = (!lean_is_exclusive(v___x_290_)) as u8;
if v_isSharedCheck_315_ == 0 {
v___x_310_ = v___x_290_;
v_isShared_311_ = v_isSharedCheck_315_;
state = 3; continue;
} else {
lean_inc(v_a_308_);
lean_dec(v___x_290_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_302_ == 0 {
lean_ctor_set(v___x_301_, 0, v___x_292_);
v___x_304_ = v___x_301_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_305_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_292_);
v___x_304_ = v_reuseFailAlloc_305_;
state = 2; continue;
}
}
3 => {
if v_isShared_311_ == 0 {
v___x_313_ = v___x_310_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_314_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mpsc___boxed(mut v_threads_316_: *mut lean_object, mut v_ch_317_: *mut lean_object, mut v_amount_318_: *mut lean_object, mut v_a_319_: *mut lean_object) -> *mut lean_object{
let mut v_res_320_: *mut lean_object = core::ptr::null_mut(); 
v_res_320_ = l_mpsc(v_threads_316_, v_ch_317_, v_amount_318_);
lean_dec(v_threads_316_);
return v_res_320_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1(mut v_upperBound_321_: *mut lean_object, mut v_amount_322_: *mut lean_object, mut v_threads_323_: *mut lean_object, mut v_ch_324_: *mut lean_object, mut v_inst_325_: *mut lean_object, mut v_R_326_: *mut lean_object, mut v_a_327_: *mut lean_object, mut v_b_328_: *mut lean_object, mut v_c_329_: *mut lean_object) -> *mut lean_object{
let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); 
v___x_331_ = l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg(v_upperBound_321_, v_amount_322_, v_threads_323_, v_ch_324_, v_a_327_, v_b_328_);
return v___x_331_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___boxed(mut v_upperBound_332_: *mut lean_object, mut v_amount_333_: *mut lean_object, mut v_threads_334_: *mut lean_object, mut v_ch_335_: *mut lean_object, mut v_inst_336_: *mut lean_object, mut v_R_337_: *mut lean_object, mut v_a_338_: *mut lean_object, mut v_b_339_: *mut lean_object, mut v_c_340_: *mut lean_object, mut v___y_341_: *mut lean_object) -> *mut lean_object{
let mut v_res_342_: *mut lean_object = core::ptr::null_mut(); 
v_res_342_ = l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1(v_upperBound_332_, v_amount_333_, v_threads_334_, v_ch_335_, v_inst_336_, v_R_337_, v_a_338_, v_b_339_, v_c_340_);
lean_dec(v_threads_334_);
lean_dec(v_amount_333_);
lean_dec(v_upperBound_332_);
return v_res_342_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00mpmc_spec__0___redArg(mut v_ch_343_: *mut lean_object) -> *mut lean_object{
let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
lean_inc_ref(v_ch_343_);
v___x_345_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_343_);
if lean_obj_tag(v___x_345_) == 1 {
lean_dec_ref_known(v___x_345_, 1);
state = 0; continue;
} else {
let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_345_);
lean_dec_ref(v_ch_343_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00mpmc_spec__0___redArg___boxed(mut v_ch_349_: *mut lean_object, mut v___y_350_: *mut lean_object) -> *mut lean_object{
let mut v_res_351_: *mut lean_object = core::ptr::null_mut(); 
v_res_351_ = l___private_Init_While_0__whileM_erased___at___00mpmc_spec__0___redArg(v_ch_349_);
return v_res_351_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg___lam__0(mut v_ch_352_: *mut lean_object, mut v___x_353_: *mut lean_object) -> *mut lean_object{
let mut v_a_356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_357_: *mut lean_object = core::ptr::null_mut(); let mut v___x_358_: *mut lean_object = core::ptr::null_mut(); let mut v_a_359_: *mut lean_object = core::ptr::null_mut(); let mut v_a_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_363_: u8 = 0; let mut v___x_365_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_366_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_367_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_358_ = l___private_Init_While_0__whileM_erased___at___00mpmc_spec__0___redArg(v_ch_352_);
if lean_obj_tag(v___x_358_) == 0 {
lean_dec_ref_known(v___x_358_, 1);
v_a_356_ = v___x_353_;
state = 1; continue;
} else {
if lean_obj_tag(v___x_358_) == 0 {
let mut v_a_359_: *mut lean_object = core::ptr::null_mut(); 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v_a_356_ = v_a_359_;
state = 1; continue;
} else {
let mut v_a_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_363_: u8 = 0; let mut v_isSharedCheck_367_: u8 = 0; 
v_a_360_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_367_ = (!lean_is_exclusive(v___x_358_)) as u8;
if v_isSharedCheck_367_ == 0 {
v___x_362_ = v___x_358_;
v_isShared_363_ = v_isSharedCheck_367_;
state = 2; continue;
} else {
lean_inc(v_a_360_);
lean_dec(v___x_358_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
state = 2; continue;
}
}
}
}
1 => {
v___x_357_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_357_, 0, v_a_356_);
return v___x_357_;
}
2 => {
if v_isShared_363_ == 0 {
lean_ctor_set_tag(v___x_362_, 0);
v___x_365_ = v___x_362_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_366_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
state = 3; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg___lam__0___boxed(mut v_ch_368_: *mut lean_object, mut v___x_369_: *mut lean_object, mut v___y_370_: *mut lean_object) -> *mut lean_object{
let mut v_res_371_: *mut lean_object = core::ptr::null_mut(); 
v_res_371_ = l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg___lam__0(v_ch_368_, v___x_369_);
return v_res_371_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg(mut v_upperBound_372_: *mut lean_object, mut v_ch_373_: *mut lean_object, mut v_a_374_: *mut lean_object, mut v_b_375_: *mut lean_object) -> *mut lean_object{
let mut v___x_377_: u8 = 0; let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v___f_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v___x_384_: *mut lean_object = core::ptr::null_mut(); let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_377_ = lean_nat_dec_lt(v_a_374_, v_upperBound_372_);
if v___x_377_ == 0 {
let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_374_);
lean_dec_ref(v_ch_373_);
v___x_378_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_378_, 0, v_b_375_);
return v___x_378_;
} else {
let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v___f_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v___x_384_: *mut lean_object = core::ptr::null_mut(); let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); 
v___x_379_ = lean_box(0);
lean_inc_ref(v_ch_373_);
v___f_380_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_380_, 0, v_ch_373_);
lean_closure_set(v___f_380_, 1, v___x_379_);
v___x_381_ = lean_unsigned_to_nat(9);
v___x_382_ = lean_io_as_task(v___f_380_, v___x_381_);
v___x_383_ = lean_array_push(v_b_375_, v___x_382_);
v___x_384_ = lean_unsigned_to_nat(1);
v___x_385_ = lean_nat_add(v_a_374_, v___x_384_);
lean_dec(v_a_374_);
v_a_374_ = v___x_385_;
v_b_375_ = v___x_383_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg___boxed(mut v_upperBound_387_: *mut lean_object, mut v_ch_388_: *mut lean_object, mut v_a_389_: *mut lean_object, mut v_b_390_: *mut lean_object, mut v___y_391_: *mut lean_object) -> *mut lean_object{
let mut v_res_392_: *mut lean_object = core::ptr::null_mut(); 
v_res_392_ = l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg(v_upperBound_387_, v_ch_388_, v_a_389_, v_b_390_);
lean_dec(v_upperBound_387_);
return v_res_392_;
}
#[no_mangle] pub unsafe extern "C" fn l_mpmc(mut v_threads_393_: *mut lean_object, mut v_ch_394_: *mut lean_object, mut v_amount_395_: *mut lean_object) -> *mut lean_object{
let mut v_producers_397_: *mut lean_object = core::ptr::null_mut(); let mut v___x_398_: *mut lean_object = core::ptr::null_mut(); let mut v___x_399_: *mut lean_object = core::ptr::null_mut(); let mut v_a_400_: *mut lean_object = core::ptr::null_mut(); let mut v___x_401_: *mut lean_object = core::ptr::null_mut(); let mut v_a_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_404_: usize = 0; let mut v___x_405_: usize = 0; let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_408_: usize = 0; let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_412_: u8 = 0; let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_415_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_416_: u8 = 0; let mut v_unused_417_: *mut lean_object = core::ptr::null_mut(); let mut v_a_418_: *mut lean_object = core::ptr::null_mut(); let mut v___x_420_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_421_: u8 = 0; let mut v___x_422_: u8 = 0; let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_425_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_426_: *mut lean_object = core::ptr::null_mut(); let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_430_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_431_: u8 = 0; let mut v_a_432_: *mut lean_object = core::ptr::null_mut(); let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_435_: u8 = 0; let mut v___x_437_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_438_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_439_: u8 = 0; let mut v_a_440_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_443_: u8 = 0; let mut v___x_445_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_446_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_447_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_producers_397_ = lean_mk_empty_array_with_capacity(v_threads_393_);
v___x_398_ = lean_unsigned_to_nat(0);
lean_inc_ref(v_producers_397_);
lean_inc_ref(v_ch_394_);
v___x_399_ = l_WellFounded_opaqueFix_u2083___at___00mpsc_spec__1___redArg(v_threads_393_, v_amount_395_, v_threads_393_, v_ch_394_, v___x_398_, v_producers_397_);
if lean_obj_tag(v___x_399_) == 0 {
let mut v_a_400_: *mut lean_object = core::ptr::null_mut(); let mut v___x_401_: *mut lean_object = core::ptr::null_mut(); 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
lean_inc_ref(v_ch_394_);
v___x_401_ = l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg(v_threads_393_, v_ch_394_, v___x_398_, v_producers_397_);
if lean_obj_tag(v___x_401_) == 0 {
let mut v_a_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_404_: usize = 0; let mut v___x_405_: usize = 0; let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = lean_box(0);
v_sz_404_ = lean_array_size(v_a_400_);
v___x_405_ = 0usize;
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mpsc_spec__0(v_a_400_, v_sz_404_, v___x_405_, v___x_403_);
lean_dec(v_a_400_);
if lean_obj_tag(v___x_406_) == 0 {
let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_406_, 1);
v___x_407_ = l_Std_CloseableChannel_close___redArg(v_ch_394_);
if lean_obj_tag(v___x_407_) == 0 {
let mut v_sz_408_: usize = 0; let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_407_, 1);
v_sz_408_ = lean_array_size(v_a_402_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mpsc_spec__0(v_a_402_, v_sz_408_, v___x_405_, v___x_403_);
lean_dec(v_a_402_);
if lean_obj_tag(v___x_409_) == 0 {
let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_412_: u8 = 0; let mut v_isSharedCheck_416_: u8 = 0; 
v_isSharedCheck_416_ = (!lean_is_exclusive(v___x_409_)) as u8;
if v_isSharedCheck_416_ == 0 {
let mut v_unused_417_: *mut lean_object = core::ptr::null_mut(); 
v_unused_417_ = lean_ctor_get(v___x_409_, 0);
lean_dec(v_unused_417_);
v___x_411_ = v___x_409_;
v_isShared_412_ = v_isSharedCheck_416_;
state = 1; continue;
} else {
lean_dec(v___x_409_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
state = 1; continue;
}
} else {
return v___x_409_;
}
} else {
let mut v_a_418_: *mut lean_object = core::ptr::null_mut(); let mut v___x_420_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_421_: u8 = 0; let mut v_isSharedCheck_431_: u8 = 0; 
lean_dec(v_a_402_);
v_a_418_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_431_ = (!lean_is_exclusive(v___x_407_)) as u8;
if v_isSharedCheck_431_ == 0 {
v___x_420_ = v___x_407_;
v_isShared_421_ = v_isSharedCheck_431_;
state = 3; continue;
} else {
lean_inc(v_a_418_);
lean_dec(v___x_407_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_431_;
state = 3; continue;
}
}
} else {
lean_dec(v_a_402_);
lean_dec_ref(v_ch_394_);
return v___x_406_;
}
} else {
let mut v_a_432_: *mut lean_object = core::ptr::null_mut(); let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_435_: u8 = 0; let mut v_isSharedCheck_439_: u8 = 0; 
lean_dec(v_a_400_);
lean_dec_ref(v_ch_394_);
v_a_432_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_439_ = (!lean_is_exclusive(v___x_401_)) as u8;
if v_isSharedCheck_439_ == 0 {
v___x_434_ = v___x_401_;
v_isShared_435_ = v_isSharedCheck_439_;
state = 6; continue;
} else {
lean_inc(v_a_432_);
lean_dec(v___x_401_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
state = 6; continue;
}
}
} else {
let mut v_a_440_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_443_: u8 = 0; let mut v_isSharedCheck_447_: u8 = 0; 
lean_dec_ref(v_producers_397_);
lean_dec_ref(v_ch_394_);
v_a_440_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_447_ = (!lean_is_exclusive(v___x_399_)) as u8;
if v_isSharedCheck_447_ == 0 {
v___x_442_ = v___x_399_;
v_isShared_443_ = v_isSharedCheck_447_;
state = 8; continue;
} else {
lean_inc(v_a_440_);
lean_dec(v___x_399_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
state = 8; continue;
}
}
}
1 => {
if v_isShared_412_ == 0 {
lean_ctor_set(v___x_411_, 0, v___x_403_);
v___x_414_ = v___x_411_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_415_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_403_);
v___x_414_ = v_reuseFailAlloc_415_;
state = 2; continue;
}
}
3 => {
v___x_422_ = (lean_unbox(v_a_418_) as u8);
lean_dec(v_a_418_);
if v___x_422_ == 0 {
let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_425_: *mut lean_object = core::ptr::null_mut(); 
v___x_423_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__1;
if v_isShared_421_ == 0 {
lean_ctor_set(v___x_420_, 0, v___x_423_);
v___x_425_ = v___x_420_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_426_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
state = 4; continue;
}
} else {
let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); 
v___x_427_ = l_WellFounded_opaqueFix_u2083___at___00seq_spec__1___redArg___closed__3;
if v_isShared_421_ == 0 {
lean_ctor_set(v___x_420_, 0, v___x_427_);
v___x_429_ = v___x_420_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_430_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
state = 5; continue;
}
}
}
6 => {
if v_isShared_435_ == 0 {
v___x_437_ = v___x_434_;
state = 7; continue;
} else {
let mut v_reuseFailAlloc_438_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
state = 7; continue;
}
}
8 => {
if v_isShared_443_ == 0 {
v___x_445_ = v___x_442_;
state = 9; continue;
} else {
let mut v_reuseFailAlloc_446_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
state = 9; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mpmc___boxed(mut v_threads_448_: *mut lean_object, mut v_ch_449_: *mut lean_object, mut v_amount_450_: *mut lean_object, mut v_a_451_: *mut lean_object) -> *mut lean_object{
let mut v_res_452_: *mut lean_object = core::ptr::null_mut(); 
v_res_452_ = l_mpmc(v_threads_448_, v_ch_449_, v_amount_450_);
lean_dec(v_amount_450_);
lean_dec(v_threads_448_);
return v_res_452_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00mpmc_spec__0(mut v_ch_453_: *mut lean_object, mut v_inst_454_: *mut lean_object, mut v_a_455_: *mut lean_object) -> *mut lean_object{
let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); 
v___x_457_ = l___private_Init_While_0__whileM_erased___at___00mpmc_spec__0___redArg(v_ch_453_);
return v___x_457_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00mpmc_spec__0___boxed(mut v_ch_458_: *mut lean_object, mut v_inst_459_: *mut lean_object, mut v_a_460_: *mut lean_object, mut v___y_461_: *mut lean_object) -> *mut lean_object{
let mut v_res_462_: *mut lean_object = core::ptr::null_mut(); 
v_res_462_ = l___private_Init_While_0__whileM_erased___at___00mpmc_spec__0(v_ch_458_, v_inst_459_, v_a_460_);
return v_res_462_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1(mut v_upperBound_463_: *mut lean_object, mut v_ch_464_: *mut lean_object, mut v_inst_465_: *mut lean_object, mut v_R_466_: *mut lean_object, mut v_a_467_: *mut lean_object, mut v_b_468_: *mut lean_object, mut v_c_469_: *mut lean_object) -> *mut lean_object{
let mut v___x_471_: *mut lean_object = core::ptr::null_mut(); 
v___x_471_ = l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___redArg(v_upperBound_463_, v_ch_464_, v_a_467_, v_b_468_);
return v___x_471_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1___boxed(mut v_upperBound_472_: *mut lean_object, mut v_ch_473_: *mut lean_object, mut v_inst_474_: *mut lean_object, mut v_R_475_: *mut lean_object, mut v_a_476_: *mut lean_object, mut v_b_477_: *mut lean_object, mut v_c_478_: *mut lean_object, mut v___y_479_: *mut lean_object) -> *mut lean_object{
let mut v_res_480_: *mut lean_object = core::ptr::null_mut(); 
v_res_480_ = l_WellFounded_opaqueFix_u2083___at___00mpmc_spec__1(v_upperBound_472_, v_ch_473_, v_inst_474_, v_R_475_, v_a_476_, v_b_477_, v_c_478_);
lean_dec(v_upperBound_472_);
return v_res_480_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00run_spec__0_spec__0(mut v_s_481_: *mut lean_object) -> *mut lean_object{
let mut v___x_483_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_484_: *mut lean_object = core::ptr::null_mut(); let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); 
v___x_483_ = lean_get_stdout();
v_putStr_484_ = lean_ctor_get(v___x_483_, 4);
lean_inc_ref(v_putStr_484_);
lean_dec_ref(v___x_483_);
v___x_485_ = lean_apply_2(v_putStr_484_, v_s_481_, lean_box(0));
return v___x_485_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00run_spec__0_spec__0___boxed(mut v_s_486_: *mut lean_object, mut v_a_487_: *mut lean_object) -> *mut lean_object{
let mut v_res_488_: *mut lean_object = core::ptr::null_mut(); 
v_res_488_ = l_IO_print___at___00IO_println___at___00run_spec__0_spec__0(v_s_486_);
return v_res_488_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00run_spec__0(mut v_s_489_: *mut lean_object) -> *mut lean_object{
let mut v___x_491_: u32 = 0; let mut v___x_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); 
v___x_491_ = 10;
v___x_492_ = lean_string_push(v_s_489_, v___x_491_);
v___x_493_ = l_IO_print___at___00IO_println___at___00run_spec__0_spec__0(v___x_492_);
return v___x_493_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00run_spec__0___boxed(mut v_s_494_: *mut lean_object, mut v_a_495_: *mut lean_object) -> *mut lean_object{
let mut v_res_496_: *mut lean_object = core::ptr::null_mut(); 
v_res_496_ = l_IO_println___at___00run_spec__0(v_s_494_);
return v_res_496_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_run___closed__0() -> f64{
let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); let mut v___x_498_: u8 = 0; let mut v___x_499_: *mut lean_object = core::ptr::null_mut(); let mut v___x_500_: f64 = 0.0; 
v___x_497_ = lean_unsigned_to_nat(1);
v___x_498_ = 1;
v___x_499_ = lean_unsigned_to_nat(10000);
v___x_500_ = l_Float_ofScientific(v___x_499_, v___x_498_, v___x_497_);
return v___x_500_;
}
#[no_mangle] pub unsafe extern "C" fn l_run(mut v_name_504_: *mut lean_object, mut v_cap_505_: *mut lean_object, mut v_messages_506_: *mut lean_object, mut v_bench_507_: *mut lean_object) -> *mut lean_object{
let mut v___x_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); 
v___x_509_ = l_Std_CloseableChannel_new___redArg(v_cap_505_);
v___x_510_ = lean_io_mono_ms_now();
v___x_511_ = lean_apply_3(v_bench_507_, v___x_509_, v_messages_506_, lean_box(0));
if lean_obj_tag(v___x_511_) == 0 {
let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v___x_513_: *mut lean_object = core::ptr::null_mut(); let mut v___x_514_: f64 = 0.0; let mut v___x_515_: f64 = 0.0; let mut v___x_516_: f64 = 0.0; let mut v___x_517_: *mut lean_object = core::ptr::null_mut(); let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); let mut v___x_519_: *mut lean_object = core::ptr::null_mut(); let mut v___x_520_: *mut lean_object = core::ptr::null_mut(); let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); let mut v___x_522_: *mut lean_object = core::ptr::null_mut(); let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); let mut v___x_524_: *mut lean_object = core::ptr::null_mut(); let mut v___x_525_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_511_, 1);
v___x_512_ = lean_io_mono_ms_now();
v___x_513_ = lean_nat_sub(v___x_512_, v___x_510_);
lean_dec(v___x_510_);
lean_dec(v___x_512_);
v___x_514_ = lean_float_of_nat(v___x_513_);
v___x_515_ = lean_float_once(core::ptr::addr_of_mut!(l_run___closed__0), core::ptr::addr_of_mut!(l_run___closed__0_once), _init_l_run___closed__0);
v___x_516_ = lean_float_div(v___x_514_, v___x_515_);
v___x_517_ = l_run___closed__1;
v___x_518_ = lean_string_append(v___x_517_, v_name_504_);
v___x_519_ = l_run___closed__2;
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
v___x_521_ = lean_float_to_string(v___x_516_);
v___x_522_ = lean_string_append(v___x_520_, v___x_521_);
lean_dec_ref(v___x_521_);
v___x_523_ = l_run___closed__3;
v___x_524_ = lean_string_append(v___x_522_, v___x_523_);
v___x_525_ = l_IO_println___at___00run_spec__0(v___x_524_);
return v___x_525_;
} else {
lean_dec(v___x_510_);
return v___x_511_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_run___boxed(mut v_name_526_: *mut lean_object, mut v_cap_527_: *mut lean_object, mut v_messages_528_: *mut lean_object, mut v_bench_529_: *mut lean_object, mut v_a_530_: *mut lean_object) -> *mut lean_object{
let mut v_res_531_: *mut lean_object = core::ptr::null_mut(); 
v_res_531_ = l_run(v_name_526_, v_cap_527_, v_messages_528_, v_bench_529_);
lean_dec_ref(v_name_526_);
return v_res_531_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_args_553_: *mut lean_object) -> *mut lean_object{
let mut v___x_555_: *mut lean_object = core::ptr::null_mut(); let mut v___x_556_: *mut lean_object = core::ptr::null_mut(); let mut v___x_557_: *mut lean_object = core::ptr::null_mut(); let mut v___x_558_: *mut lean_object = core::ptr::null_mut(); let mut v___x_559_: *mut lean_object = core::ptr::null_mut(); let mut v___x_560_: *mut lean_object = core::ptr::null_mut(); let mut v___x_561_: *mut lean_object = core::ptr::null_mut(); let mut v_messages_562_: *mut lean_object = core::ptr::null_mut(); let mut v___x_563_: *mut lean_object = core::ptr::null_mut(); let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_565_: *mut lean_object = core::ptr::null_mut(); let mut v___x_566_: *mut lean_object = core::ptr::null_mut(); let mut v___x_567_: *mut lean_object = core::ptr::null_mut(); let mut v___x_568_: *mut lean_object = core::ptr::null_mut(); let mut v_threads_569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_570_: *mut lean_object = core::ptr::null_mut(); let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); let mut v___x_572_: *mut lean_object = core::ptr::null_mut(); let mut v___x_573_: *mut lean_object = core::ptr::null_mut(); let mut v___x_574_: *mut lean_object = core::ptr::null_mut(); let mut v___x_575_: *mut lean_object = core::ptr::null_mut(); let mut v___x_576_: *mut lean_object = core::ptr::null_mut(); let mut v___x_577_: *mut lean_object = core::ptr::null_mut(); let mut v___x_578_: *mut lean_object = core::ptr::null_mut(); let mut v___x_579_: *mut lean_object = core::ptr::null_mut(); let mut v___x_580_: *mut lean_object = core::ptr::null_mut(); let mut v___x_581_: *mut lean_object = core::ptr::null_mut(); let mut v___x_582_: *mut lean_object = core::ptr::null_mut(); let mut v___x_584_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_585_: u8 = 0; let mut v___x_586_: *mut lean_object = core::ptr::null_mut(); let mut v___x_588_: *mut lean_object = core::ptr::null_mut(); let mut v___x_589_: *mut lean_object = core::ptr::null_mut(); let mut v___x_590_: *mut lean_object = core::ptr::null_mut(); let mut v___x_591_: *mut lean_object = core::ptr::null_mut(); let mut v___x_592_: *mut lean_object = core::ptr::null_mut(); let mut v___x_593_: *mut lean_object = core::ptr::null_mut(); let mut v___x_594_: *mut lean_object = core::ptr::null_mut(); let mut v___x_595_: *mut lean_object = core::ptr::null_mut(); let mut v___x_596_: *mut lean_object = core::ptr::null_mut(); let mut v___x_597_: *mut lean_object = core::ptr::null_mut(); let mut v___x_598_: *mut lean_object = core::ptr::null_mut(); let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); let mut v___x_600_: *mut lean_object = core::ptr::null_mut(); let mut v___x_601_: *mut lean_object = core::ptr::null_mut(); let mut v___x_602_: *mut lean_object = core::ptr::null_mut(); let mut v___x_603_: *mut lean_object = core::ptr::null_mut(); let mut v___x_604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_605_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_606_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_607_: u8 = 0; let mut v_unused_608_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_555_ = l_main___closed__0;
v___x_556_ = lean_unsigned_to_nat(0);
v___x_557_ = l_List_get_x21Internal___redArg(v___x_555_, v_args_553_, v___x_556_);
v___x_558_ = lean_unsigned_to_nat(1);
v___x_559_ = l_List_get_x21Internal___redArg(v___x_555_, v_args_553_, v___x_558_);
lean_dec(v_args_553_);
v___x_560_ = lean_string_utf8_byte_size(v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_556_);
lean_ctor_set(v___x_561_, 2, v___x_560_);
v_messages_562_ = l_String_Slice_toNat_x21(v___x_561_);
lean_dec_ref_known(v___x_561_, 3);
v___x_563_ = l_main___closed__1;
v___x_564_ = l_main___closed__2;
v___x_565_ = l_main___closed__3;
lean_inc(v_messages_562_);
v___x_566_ = l_run(v___x_563_, v___x_564_, v_messages_562_, v___x_565_);
if lean_obj_tag(v___x_566_) == 0 {
let mut v___x_567_: *mut lean_object = core::ptr::null_mut(); let mut v___x_568_: *mut lean_object = core::ptr::null_mut(); let mut v_threads_569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_570_: *mut lean_object = core::ptr::null_mut(); let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); let mut v___x_572_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_566_, 1);
v___x_567_ = lean_string_utf8_byte_size(v___x_557_);
v___x_568_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_568_, 0, v___x_557_);
lean_ctor_set(v___x_568_, 1, v___x_556_);
lean_ctor_set(v___x_568_, 2, v___x_567_);
v_threads_569_ = l_String_Slice_toNat_x21(v___x_568_);
lean_dec_ref_known(v___x_568_, 3);
v___x_570_ = l_main___closed__4;
lean_inc(v_threads_569_);
v___x_571_ = lean_alloc_closure(l_mpsc___boxed as *mut core::ffi::c_void, 4, 1);
lean_closure_set(v___x_571_, 0, v_threads_569_);
lean_inc_ref(v___x_571_);
lean_inc(v_messages_562_);
v___x_572_ = l_run(v___x_570_, v___x_564_, v_messages_562_, v___x_571_);
if lean_obj_tag(v___x_572_) == 0 {
let mut v___x_573_: *mut lean_object = core::ptr::null_mut(); let mut v___x_574_: *mut lean_object = core::ptr::null_mut(); let mut v___x_575_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_572_, 1);
v___x_573_ = l_main___closed__5;
v___x_574_ = lean_alloc_closure(l_mpmc___boxed as *mut core::ffi::c_void, 4, 1);
lean_closure_set(v___x_574_, 0, v_threads_569_);
lean_inc_ref(v___x_574_);
lean_inc(v_messages_562_);
v___x_575_ = l_run(v___x_573_, v___x_564_, v_messages_562_, v___x_574_);
if lean_obj_tag(v___x_575_) == 0 {
let mut v___x_576_: *mut lean_object = core::ptr::null_mut(); let mut v___x_577_: *mut lean_object = core::ptr::null_mut(); let mut v___x_578_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_575_, 1);
v___x_576_ = l_main___closed__6;
v___x_577_ = l_main___closed__7;
lean_inc(v_messages_562_);
v___x_578_ = l_run(v___x_576_, v___x_577_, v_messages_562_, v___x_565_);
if lean_obj_tag(v___x_578_) == 0 {
let mut v___x_579_: *mut lean_object = core::ptr::null_mut(); let mut v___x_580_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_578_, 1);
v___x_579_ = l_main___closed__8;
lean_inc_ref(v___x_571_);
lean_inc(v_messages_562_);
v___x_580_ = l_run(v___x_579_, v___x_577_, v_messages_562_, v___x_571_);
if lean_obj_tag(v___x_580_) == 0 {
let mut v___x_581_: *mut lean_object = core::ptr::null_mut(); let mut v___x_582_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_580_, 1);
v___x_581_ = l_main___closed__9;
lean_inc_ref(v___x_574_);
lean_inc(v_messages_562_);
v___x_582_ = l_run(v___x_581_, v___x_577_, v_messages_562_, v___x_574_);
if lean_obj_tag(v___x_582_) == 0 {
let mut v___x_584_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_585_: u8 = 0; let mut v_isSharedCheck_607_: u8 = 0; 
v_isSharedCheck_607_ = (!lean_is_exclusive(v___x_582_)) as u8;
if v_isSharedCheck_607_ == 0 {
let mut v_unused_608_: *mut lean_object = core::ptr::null_mut(); 
v_unused_608_ = lean_ctor_get(v___x_582_, 0);
lean_dec(v_unused_608_);
v___x_584_ = v___x_582_;
v_isShared_585_ = v_isSharedCheck_607_;
state = 1; continue;
} else {
lean_dec(v___x_582_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_607_;
state = 1; continue;
}
} else {
lean_dec_ref(v___x_574_);
lean_dec_ref(v___x_571_);
lean_dec(v_messages_562_);
return v___x_582_;
}
} else {
lean_dec_ref(v___x_574_);
lean_dec_ref(v___x_571_);
lean_dec(v_messages_562_);
return v___x_580_;
}
} else {
lean_dec_ref(v___x_574_);
lean_dec_ref(v___x_571_);
lean_dec(v_messages_562_);
return v___x_578_;
}
} else {
lean_dec_ref(v___x_574_);
lean_dec_ref(v___x_571_);
lean_dec(v_messages_562_);
return v___x_575_;
}
} else {
lean_dec_ref(v___x_571_);
lean_dec(v_threads_569_);
lean_dec(v_messages_562_);
return v___x_572_;
}
} else {
lean_dec(v_messages_562_);
lean_dec(v___x_557_);
return v___x_566_;
}
}
1 => {
v___x_586_ = l_main___closed__10;
lean_inc(v_messages_562_);
if v_isShared_585_ == 0 {
lean_ctor_set_tag(v___x_584_, 1);
lean_ctor_set(v___x_584_, 0, v_messages_562_);
v___x_588_ = v___x_584_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_606_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_messages_562_);
v___x_588_ = v_reuseFailAlloc_606_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_args_609_: *mut lean_object, mut v_a_610_: *mut lean_object) -> *mut lean_object{
let mut v_res_611_: *mut lean_object = core::ptr::null_mut(); 
v_res_611_ = _lean_main(v_args_609_);
return v_res_611_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Sync_Channel(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_channel(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Sync_Channel(builtin);
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
  let res = initialize_channel(1 /* builtin */);
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
