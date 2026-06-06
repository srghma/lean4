// Lean compiler output
// Module: overflow2
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_StateT_instMonad___redArg___lam__1(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_instMonad___redArg___lam__4(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_instMonad___redArg___lam__7(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_instMonad___redArg___lam__9(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_map(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_pure(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_bind(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_instInhabitedOfMonad___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_dec_eq(_: u32, _: u32) -> u8;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_panic___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_usize_of_nat(_: *mut lean_object) -> usize;
    fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: usize, _: usize, _: *mut lean_object) -> *mut lean_object;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_usize_dec_eq(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn l_Id_instMonad___lam__0(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__1___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__2___boxed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__3(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__4___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__5___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__6(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_panic_fn_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
}
#[no_mangle] pub static mut l_longArray___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_OverflowFold___redArg___lam__0___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [122, 0]};
static mut l_OverflowFold___redArg___lam__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_OverflowFold___redArg___lam__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__1_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__2_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__2: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__3_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__3: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__4_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__4: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__5_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__5: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__6_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__6: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn _init_l_longArray___boxed__const__1() -> *mut lean_object{
let mut v___x_1_: u32 = 0; let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); 
v___x_1_ = 97;
v___x_2_ = lean_box_uint32(v___x_1_);
return v___x_2_;
}
#[no_mangle] pub unsafe extern "C" fn l_longArray(mut v_n_3_: *mut lean_object, mut v_xs_4_: *mut lean_object) -> *mut lean_object{
let mut v_zero_5_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_6_: u8 = 0; let mut v_one_7_: *mut lean_object = core::ptr::null_mut(); let mut v_n_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_5_ = lean_unsigned_to_nat(0);
v_isZero_6_ = lean_nat_dec_eq(v_n_3_, v_zero_5_);
if v_isZero_6_ == 1 {
lean_dec(v_n_3_);
return v_xs_4_;
} else {
let mut v_one_7_: *mut lean_object = core::ptr::null_mut(); let mut v_n_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); 
v_one_7_ = lean_unsigned_to_nat(1);
v_n_8_ = lean_nat_sub(v_n_3_, v_one_7_);
lean_dec(v_n_3_);
v___x_9_ = l_longArray___boxed__const__1;
v___x_10_ = lean_array_push(v_xs_4_, v___x_9_);
v_n_3_ = v_n_8_;
v_xs_4_ = v___x_10_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowFold___redArg___lam__0(mut v_inst1_13_: *mut lean_object, mut v___x_14_: *mut lean_object, mut v_len_15_: *mut lean_object, mut v_s_16_: u32, mut v___y_17_: *mut lean_object) -> *mut lean_object{
let mut v___x_18_: u32 = 0; let mut v___x_19_: u8 = 0; let mut v_toApplicative_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_23_: u8 = 0; let mut v_toPure_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_30_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_31_: u8 = 0; let mut v_unused_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_447__overap_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_18_ = 122;
v___x_19_ = lean_uint32_dec_eq(v_s_16_, v___x_18_);
if v___x_19_ == 0 {
let mut v_toApplicative_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_23_: u8 = 0; let mut v_isSharedCheck_31_: u8 = 0; 
v_toApplicative_20_ = lean_ctor_get(v_inst1_13_, 0);
v_isSharedCheck_31_ = (!lean_is_exclusive(v_inst1_13_)) as u8;
if v_isSharedCheck_31_ == 0 {
let mut v_unused_32_: *mut lean_object = core::ptr::null_mut(); 
v_unused_32_ = lean_ctor_get(v_inst1_13_, 1);
lean_dec(v_unused_32_);
v___x_22_ = v_inst1_13_;
v_isShared_23_ = v_isSharedCheck_31_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_20_);
lean_dec(v_inst1_13_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_31_;
state = 1; continue;
}
} else {
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_447__overap_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_inst1_13_);
v___x_33_ = l_OverflowFold___redArg___lam__0___closed__0;
v___x_447__overap_34_ = l_panic___redArg(v___x_14_, v___x_33_);
v___x_35_ = lean_apply_1(v___x_447__overap_34_, v___y_17_);
return v___x_35_;
}
}
1 => {
v_toPure_24_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_inc(v_toPure_24_);
lean_dec_ref(v_toApplicative_20_);
v___x_25_ = lean_unsigned_to_nat(1);
v___x_26_ = lean_nat_add(v_len_15_, v___x_25_);
if v_isShared_23_ == 0 {
lean_ctor_set(v___x_22_, 1, v___y_17_);
lean_ctor_set(v___x_22_, 0, v___x_26_);
v___x_28_ = v___x_22_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_30_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___y_17_);
v___x_28_ = v_reuseFailAlloc_30_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowFold___redArg___lam__0___boxed(mut v_inst1_36_: *mut lean_object, mut v___x_37_: *mut lean_object, mut v_len_38_: *mut lean_object, mut v_s_39_: *mut lean_object, mut v___y_40_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_41_: u32 = 0; let mut v_res_42_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_41_ = lean_unbox_uint32(v_s_39_);
lean_dec(v_s_39_);
v_res_42_ = l_OverflowFold___redArg___lam__0(v_inst1_36_, v___x_37_, v_len_38_, v_s_boxed_41_, v___y_40_);
lean_dec(v_len_38_);
lean_dec(v___x_37_);
return v_res_42_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowFold___redArg(mut v_inst1_43_: *mut lean_object, mut v_xs_44_: *mut lean_object, mut v_a_45_: *mut lean_object) -> *mut lean_object{
let mut v___f_46_: *mut lean_object = core::ptr::null_mut(); let mut v___f_47_: *mut lean_object = core::ptr::null_mut(); let mut v___f_48_: *mut lean_object = core::ptr::null_mut(); let mut v___f_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: u8 = 0; let mut v_toApplicative_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_62_: u8 = 0; let mut v_toPure_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_67_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_68_: u8 = 0; let mut v_unused_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___f_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: u8 = 0; let mut v_toApplicative_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_76_: u8 = 0; let mut v_toPure_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_81_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_82_: u8 = 0; let mut v_unused_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: usize = 0; let mut v___x_85_: usize = 0; let mut v___x_408__overap_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: usize = 0; let mut v___x_89_: usize = 0; let mut v___x_413__overap_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
lean_inc_ref_n(v_inst1_43_, 7);
v___f_46_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_46_, 0, v_inst1_43_);
v___f_47_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_47_, 0, v_inst1_43_);
v___f_48_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_48_, 0, v_inst1_43_);
v___f_49_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_49_, 0, v_inst1_43_);
v___x_50_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_50_, 0, lean_box(0));
lean_closure_set(v___x_50_, 1, lean_box(0));
lean_closure_set(v___x_50_, 2, v_inst1_43_);
v___x_51_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___f_46_);
v___x_52_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
lean_closure_set(v___x_52_, 0, lean_box(0));
lean_closure_set(v___x_52_, 1, lean_box(0));
lean_closure_set(v___x_52_, 2, v_inst1_43_);
v___x_53_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_53_, 0, v___x_51_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
lean_ctor_set(v___x_53_, 2, v___f_47_);
lean_ctor_set(v___x_53_, 3, v___f_48_);
lean_ctor_set(v___x_53_, 4, v___f_49_);
v___x_54_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_54_, 0, lean_box(0));
lean_closure_set(v___x_54_, 1, lean_box(0));
lean_closure_set(v___x_54_, 2, v_inst1_43_);
v___x_55_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_unsigned_to_nat(0);
v___x_57_ = lean_array_get_size(v_xs_44_);
v___x_58_ = lean_nat_dec_lt(v___x_56_, v___x_57_);
if v___x_58_ == 0 {
let mut v_toApplicative_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_62_: u8 = 0; let mut v_isSharedCheck_68_: u8 = 0; 
lean_dec_ref_known(v___x_55_, 2);
lean_dec_ref(v_xs_44_);
v_toApplicative_59_ = lean_ctor_get(v_inst1_43_, 0);
v_isSharedCheck_68_ = (!lean_is_exclusive(v_inst1_43_)) as u8;
if v_isSharedCheck_68_ == 0 {
let mut v_unused_69_: *mut lean_object = core::ptr::null_mut(); 
v_unused_69_ = lean_ctor_get(v_inst1_43_, 1);
lean_dec(v_unused_69_);
v___x_61_ = v_inst1_43_;
v_isShared_62_ = v_isSharedCheck_68_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_59_);
lean_dec(v_inst1_43_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_68_;
state = 1; continue;
}
} else {
let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___f_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: u8 = 0; 
lean_inc_ref(v___x_55_);
v___x_70_ = l_instInhabitedOfMonad___redArg(v___x_55_, v___x_56_);
lean_inc_ref(v_inst1_43_);
v___f_71_ = lean_alloc_closure(l_OverflowFold___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
lean_closure_set(v___f_71_, 0, v_inst1_43_);
lean_closure_set(v___f_71_, 1, v___x_70_);
v___x_72_ = lean_nat_dec_le(v___x_57_, v___x_57_);
if v___x_72_ == 0 {
if v___x_58_ == 0 {
let mut v_toApplicative_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_76_: u8 = 0; let mut v_isSharedCheck_82_: u8 = 0; 
lean_dec_ref(v___f_71_);
lean_dec_ref_known(v___x_55_, 2);
lean_dec_ref(v_xs_44_);
v_toApplicative_73_ = lean_ctor_get(v_inst1_43_, 0);
v_isSharedCheck_82_ = (!lean_is_exclusive(v_inst1_43_)) as u8;
if v_isSharedCheck_82_ == 0 {
let mut v_unused_83_: *mut lean_object = core::ptr::null_mut(); 
v_unused_83_ = lean_ctor_get(v_inst1_43_, 1);
lean_dec(v_unused_83_);
v___x_75_ = v_inst1_43_;
v_isShared_76_ = v_isSharedCheck_82_;
state = 3; continue;
} else {
lean_inc(v_toApplicative_73_);
lean_dec(v_inst1_43_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_82_;
state = 3; continue;
}
} else {
let mut v___x_84_: usize = 0; let mut v___x_85_: usize = 0; let mut v___x_408__overap_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_inst1_43_);
v___x_84_ = 0usize;
v___x_85_ = lean_usize_of_nat(v___x_57_);
v___x_408__overap_86_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_55_, v___f_71_, v_xs_44_, v___x_84_, v___x_85_, v___x_56_);
v___x_87_ = lean_apply_1(v___x_408__overap_86_, v_a_45_);
return v___x_87_;
}
} else {
let mut v___x_88_: usize = 0; let mut v___x_89_: usize = 0; let mut v___x_413__overap_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_inst1_43_);
v___x_88_ = 0usize;
v___x_89_ = lean_usize_of_nat(v___x_57_);
v___x_413__overap_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_55_, v___f_71_, v_xs_44_, v___x_88_, v___x_89_, v___x_56_);
v___x_91_ = lean_apply_1(v___x_413__overap_90_, v_a_45_);
return v___x_91_;
}
}
}
1 => {
v_toPure_63_ = lean_ctor_get(v_toApplicative_59_, 1);
lean_inc(v_toPure_63_);
lean_dec_ref(v_toApplicative_59_);
if v_isShared_62_ == 0 {
lean_ctor_set(v___x_61_, 1, v_a_45_);
lean_ctor_set(v___x_61_, 0, v___x_56_);
v___x_65_ = v___x_61_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_67_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_a_45_);
v___x_65_ = v_reuseFailAlloc_67_;
state = 2; continue;
}
}
3 => {
v_toPure_77_ = lean_ctor_get(v_toApplicative_73_, 1);
lean_inc(v_toPure_77_);
lean_dec_ref(v_toApplicative_73_);
if v_isShared_76_ == 0 {
lean_ctor_set(v___x_75_, 1, v_a_45_);
lean_ctor_set(v___x_75_, 0, v___x_56_);
v___x_79_ = v___x_75_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_81_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_a_45_);
v___x_79_ = v_reuseFailAlloc_81_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowFold(mut v_m_92_: *mut lean_object, mut v_inst1_93_: *mut lean_object, mut v_xs_94_: *mut lean_object, mut v_a_95_: *mut lean_object) -> *mut lean_object{
let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); 
v___x_96_ = l_OverflowFold___redArg(v_inst1_93_, v_xs_94_, v_a_95_);
return v___x_96_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(mut v_s_97_: *mut lean_object) -> *mut lean_object{
let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); 
v___x_99_ = lean_get_stdout();
v_putStr_100_ = lean_ctor_get(v___x_99_, 4);
lean_inc_ref(v_putStr_100_);
lean_dec_ref(v___x_99_);
v___x_101_ = lean_apply_2(v_putStr_100_, v_s_97_, lean_box(0));
return v___x_101_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__3___boxed(mut v_s_102_: *mut lean_object, mut v_a_103_: *mut lean_object) -> *mut lean_object{
let mut v_res_104_: *mut lean_object = core::ptr::null_mut(); 
v_res_104_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(v_s_102_);
return v_res_104_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_105_: *mut lean_object) -> *mut lean_object{
let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: u32 = 0; let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); 
v___x_107_ = l_Nat_reprFast(v_s_105_);
v___x_108_ = 10;
v___x_109_ = lean_string_push(v___x_107_, v___x_108_);
v___x_110_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(v___x_109_);
return v___x_110_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_111_: *mut lean_object, mut v_a_112_: *mut lean_object) -> *mut lean_object{
let mut v_res_113_: *mut lean_object = core::ptr::null_mut(); 
v_res_113_ = l_IO_println___at___00main_spec__1(v_s_111_);
return v_res_113_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00OverflowFold___at___00main_spec__0_spec__0(mut v_msg_121_: *mut lean_object, mut v___y_122_: *mut lean_object) -> *mut lean_object{
let mut v___f_123_: *mut lean_object = core::ptr::null_mut(); let mut v___f_124_: *mut lean_object = core::ptr::null_mut(); let mut v___f_125_: *mut lean_object = core::ptr::null_mut(); let mut v___f_126_: *mut lean_object = core::ptr::null_mut(); let mut v___f_127_: *mut lean_object = core::ptr::null_mut(); let mut v___f_128_: *mut lean_object = core::ptr::null_mut(); let mut v___f_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___f_133_: *mut lean_object = core::ptr::null_mut(); let mut v___f_134_: *mut lean_object = core::ptr::null_mut(); let mut v___f_135_: *mut lean_object = core::ptr::null_mut(); let mut v___f_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_250__overap_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); 
v___f_123_ = l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__0;
v___f_124_ = l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__1;
v___f_125_ = l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__2;
v___f_126_ = l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__3;
v___f_127_ = l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__4;
v___f_128_ = l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__5;
v___f_129_ = l_panic___at___00OverflowFold___at___00main_spec__0_spec__0___closed__6;
v___x_130_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_130_, 0, v___f_123_);
lean_ctor_set(v___x_130_, 1, v___f_124_);
v___x_131_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___f_125_);
lean_ctor_set(v___x_131_, 2, v___f_126_);
lean_ctor_set(v___x_131_, 3, v___f_127_);
lean_ctor_set(v___x_131_, 4, v___f_128_);
v___x_132_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___f_129_);
lean_inc_ref_n(v___x_132_, 6);
v___f_133_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_133_, 0, v___x_132_);
v___f_134_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_134_, 0, v___x_132_);
v___f_135_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_135_, 0, v___x_132_);
v___f_136_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_136_, 0, v___x_132_);
v___x_137_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_137_, 0, lean_box(0));
lean_closure_set(v___x_137_, 1, lean_box(0));
lean_closure_set(v___x_137_, 2, v___x_132_);
v___x_138_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___f_133_);
v___x_139_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
lean_closure_set(v___x_139_, 0, lean_box(0));
lean_closure_set(v___x_139_, 1, lean_box(0));
lean_closure_set(v___x_139_, 2, v___x_132_);
v___x_140_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
lean_ctor_set(v___x_140_, 2, v___f_134_);
lean_ctor_set(v___x_140_, 3, v___f_135_);
lean_ctor_set(v___x_140_, 4, v___f_136_);
v___x_141_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_141_, 0, lean_box(0));
lean_closure_set(v___x_141_, 1, lean_box(0));
lean_closure_set(v___x_141_, 2, v___x_132_);
v___x_142_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(0);
v___x_144_ = l_instInhabitedOfMonad___redArg(v___x_142_, v___x_143_);
v___x_250__overap_145_ = lean_panic_fn_borrowed(v___x_144_, v_msg_121_);
lean_dec(v___x_144_);
v___x_146_ = lean_apply_1(v___x_250__overap_145_, v___y_122_);
return v___x_146_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowFold___at___00main_spec__0_spec__1(mut v_as_147_: *mut lean_object, mut v_i_148_: usize, mut v_stop_149_: usize, mut v_b_150_: *mut lean_object, mut v___y_151_: *mut lean_object) -> *mut lean_object{
let mut v_fst_153_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: usize = 0; let mut v___x_156_: usize = 0; let mut v___x_158_: u8 = 0; let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: u32 = 0; let mut v___x_161_: u32 = 0; let mut v___x_162_: u8 = 0; let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_167_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_158_ = lean_usize_dec_eq(v_i_148_, v_stop_149_);
if v___x_158_ == 0 {
let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: u32 = 0; let mut v___x_161_: u32 = 0; let mut v___x_162_: u8 = 0; 
v___x_159_ = lean_array_uget_borrowed(v_as_147_, v_i_148_);
v___x_160_ = 122;
v___x_161_ = lean_unbox_uint32(v___x_159_);
v___x_162_ = lean_uint32_dec_eq(v___x_161_, v___x_160_);
if v___x_162_ == 0 {
let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); 
v___x_163_ = lean_unsigned_to_nat(1);
v___x_164_ = lean_nat_add(v_b_150_, v___x_163_);
lean_dec(v_b_150_);
v_fst_153_ = v___x_164_;
v_snd_154_ = v___y_151_;
state = 1; continue;
} else {
let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_167_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_168_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_b_150_);
v___x_165_ = l_OverflowFold___redArg___lam__0___closed__0;
v___x_166_ = l_panic___at___00OverflowFold___at___00main_spec__0_spec__0(v___x_165_, v___y_151_);
v_fst_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_fst_167_);
v_snd_168_ = lean_ctor_get(v___x_166_, 1);
lean_inc(v_snd_168_);
lean_dec_ref(v___x_166_);
v_fst_153_ = v_fst_167_;
v_snd_154_ = v_snd_168_;
state = 1; continue;
}
} else {
let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
v___x_169_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_169_, 0, v_b_150_);
lean_ctor_set(v___x_169_, 1, v___y_151_);
return v___x_169_;
}
}
1 => {
v___x_155_ = 1usize;
v___x_156_ = lean_usize_add(v_i_148_, v___x_155_);
v_i_148_ = v___x_156_;
v_b_150_ = v_fst_153_;
v___y_151_ = v_snd_154_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowFold___at___00main_spec__0_spec__1___boxed(mut v_as_170_: *mut lean_object, mut v_i_171_: *mut lean_object, mut v_stop_172_: *mut lean_object, mut v_b_173_: *mut lean_object, mut v___y_174_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_175_: usize = 0; let mut v_stop_boxed_176_: usize = 0; let mut v_res_177_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_175_ = lean_unbox_usize(v_i_171_);
lean_dec(v_i_171_);
v_stop_boxed_176_ = lean_unbox_usize(v_stop_172_);
lean_dec(v_stop_172_);
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowFold___at___00main_spec__0_spec__1(v_as_170_, v_i_boxed_175_, v_stop_boxed_176_, v_b_173_, v___y_174_);
lean_dec_ref(v_as_170_);
return v_res_177_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowFold___at___00main_spec__0(mut v_xs_178_: *mut lean_object, mut v_a_179_: *mut lean_object) -> *mut lean_object{
let mut v___x_180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v___x_182_: u8 = 0; 
v___x_180_ = lean_unsigned_to_nat(0);
v___x_181_ = lean_array_get_size(v_xs_178_);
v___x_182_ = lean_nat_dec_lt(v___x_180_, v___x_181_);
if v___x_182_ == 0 {
let mut v___x_183_: *mut lean_object = core::ptr::null_mut(); 
v___x_183_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_183_, 0, v___x_180_);
lean_ctor_set(v___x_183_, 1, v_a_179_);
return v___x_183_;
} else {
let mut v___x_184_: u8 = 0; 
v___x_184_ = lean_nat_dec_le(v___x_181_, v___x_181_);
if v___x_184_ == 0 {
if v___x_182_ == 0 {
let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); 
v___x_185_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_185_, 0, v___x_180_);
lean_ctor_set(v___x_185_, 1, v_a_179_);
return v___x_185_;
} else {
let mut v___x_186_: usize = 0; let mut v___x_187_: usize = 0; let mut v___x_188_: *mut lean_object = core::ptr::null_mut(); 
v___x_186_ = 0usize;
v___x_187_ = lean_usize_of_nat(v___x_181_);
v___x_188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowFold___at___00main_spec__0_spec__1(v_xs_178_, v___x_186_, v___x_187_, v___x_180_, v_a_179_);
return v___x_188_;
}
} else {
let mut v___x_189_: usize = 0; let mut v___x_190_: usize = 0; let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); 
v___x_189_ = 0usize;
v___x_190_ = lean_usize_of_nat(v___x_181_);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowFold___at___00main_spec__0_spec__1(v_xs_178_, v___x_189_, v___x_190_, v___x_180_, v_a_179_);
return v___x_191_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowFold___at___00main_spec__0___boxed(mut v_xs_192_: *mut lean_object, mut v_a_193_: *mut lean_object) -> *mut lean_object{
let mut v_res_194_: *mut lean_object = core::ptr::null_mut(); 
v_res_194_ = l_OverflowFold___at___00main_spec__0(v_xs_192_, v_a_193_);
lean_dec_ref(v_xs_192_);
return v_res_194_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); 
v___x_197_ = l_main___closed__0;
v___x_198_ = lean_unsigned_to_nat(50000);
v___x_199_ = l_longArray(v___x_198_, v___x_197_);
return v___x_199_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); 
v___x_200_ = lean_unsigned_to_nat(0);
v___x_201_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_202_ = l_OverflowFold___at___00main_spec__0(v___x_201_, v___x_200_);
return v___x_202_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); 
v___x_204_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v_fst_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_fst_205_);
v___x_206_ = l_IO_println___at___00main_spec__1(v_fst_205_);
return v___x_206_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_207_: *mut lean_object) -> *mut lean_object{
let mut v_res_208_: *mut lean_object = core::ptr::null_mut(); 
v_res_208_ = _lean_main();
return v_res_208_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_overflow2(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_longArray___boxed__const__1 = _init_l_longArray___boxed__const__1();
lean_mark_persistent(l_longArray___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_overflow2(1 /* builtin */);
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
