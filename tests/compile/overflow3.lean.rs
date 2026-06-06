// Lean compiler output
// Module: overflow3
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_array_size(_: *mut lean_object) -> usize;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_usize_dec_lt(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_uint32_dec_eq(_: u32, _: u32) -> u8;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__0(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__1___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__2___boxed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__3(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__4___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__5___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Id_instMonad___lam__6(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_instMonad___redArg___lam__1(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_instMonad___redArg___lam__4(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_instMonad___redArg___lam__7(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_instMonad___redArg___lam__9(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_map(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_pure(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_StateT_bind(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_instInhabitedOfMonad___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_panic_fn_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn l_panic___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: usize, _: usize, _: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static mut l_longArray___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_OverflowLoop___redArg___lam__2___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [122, 0]};
static mut l_OverflowLoop___redArg___lam__2___closed__0: *mut lean_object = core::ptr::addr_of!(l_OverflowLoop___redArg___lam__2___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__1_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__2_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__2: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__3_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__3: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__4_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__4: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__5_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__5: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__6_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__6: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__6_value) as *mut lean_object;
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
#[no_mangle] pub unsafe extern "C" fn l_OverflowLoop___redArg___lam__0(mut v_toApplicative_12_: *mut lean_object, mut v_____x_13_: *mut lean_object) -> *mut lean_object{
let mut v_toPure_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v_toPure_14_ = lean_ctor_get(v_toApplicative_12_, 1);
lean_inc(v_toPure_14_);
lean_dec_ref(v_toApplicative_12_);
v___x_15_ = lean_apply_2(v_toPure_14_, lean_box(0), v_____x_13_);
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowLoop___redArg___lam__1(mut v_toApplicative_16_: *mut lean_object, mut v___y_17_: *mut lean_object, mut v_____x_18_: *mut lean_object) -> *mut lean_object{
let mut v_snd_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_22_: u8 = 0; let mut v_toPure_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_28_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_29_: u8 = 0; let mut v_unused_30_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_snd_19_ = lean_ctor_get(v_____x_18_, 1);
v_isSharedCheck_29_ = (!lean_is_exclusive(v_____x_18_)) as u8;
if v_isSharedCheck_29_ == 0 {
let mut v_unused_30_: *mut lean_object = core::ptr::null_mut(); 
v_unused_30_ = lean_ctor_get(v_____x_18_, 0);
lean_dec(v_unused_30_);
v___x_21_ = v_____x_18_;
v_isShared_22_ = v_isSharedCheck_29_;
state = 1; continue;
} else {
lean_inc(v_snd_19_);
lean_dec(v_____x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_29_;
state = 1; continue;
}
}
1 => {
v_toPure_23_ = lean_ctor_get(v_toApplicative_16_, 1);
lean_inc(v_toPure_23_);
lean_dec_ref(v_toApplicative_16_);
v___x_24_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_24_, 0, v___y_17_);
if v_isShared_22_ == 0 {
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_26_ = v___x_21_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_28_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_snd_19_);
v___x_26_ = v_reuseFailAlloc_28_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowLoop___redArg___lam__2(mut v_toApplicative_32_: *mut lean_object, mut v___x_33_: *mut lean_object, mut v_toBind_34_: *mut lean_object, mut v_a_35_: u32, mut v_x_36_: *mut lean_object, mut v___y_37_: *mut lean_object, mut v___y_38_: *mut lean_object) -> *mut lean_object{
let mut v___x_39_: u32 = 0; let mut v___x_40_: u8 = 0; 
v___x_39_ = 122;
v___x_40_ = lean_uint32_dec_eq(v_a_35_, v___x_39_);
if v___x_40_ == 0 {
let mut v_toPure_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_toBind_34_);
v_toPure_41_ = lean_ctor_get(v_toApplicative_32_, 1);
lean_inc(v_toPure_41_);
lean_dec_ref(v_toApplicative_32_);
v___x_42_ = lean_unsigned_to_nat(1);
v___x_43_ = lean_nat_add(v___y_37_, v___x_42_);
lean_dec(v___y_37_);
v___x_44_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_44_, 0, v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___y_38_);
v___x_46_ = lean_apply_2(v_toPure_41_, lean_box(0), v___x_45_);
return v___x_46_;
} else {
let mut v___f_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_668__overap_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
v___f_47_ = lean_alloc_closure(l_OverflowLoop___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_47_, 0, v_toApplicative_32_);
lean_closure_set(v___f_47_, 1, v___y_37_);
v___x_48_ = l_OverflowLoop___redArg___lam__2___closed__0;
v___x_668__overap_49_ = l_panic___redArg(v___x_33_, v___x_48_);
v___x_50_ = lean_apply_1(v___x_668__overap_49_, v___y_38_);
v___x_51_ = lean_apply_4(v_toBind_34_, lean_box(0), lean_box(0), v___x_50_, v___f_47_);
return v___x_51_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowLoop___redArg___lam__2___boxed(mut v_toApplicative_52_: *mut lean_object, mut v___x_53_: *mut lean_object, mut v_toBind_54_: *mut lean_object, mut v_a_55_: *mut lean_object, mut v_x_56_: *mut lean_object, mut v___y_57_: *mut lean_object, mut v___y_58_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_59_: u32 = 0; let mut v_res_60_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_59_ = lean_unbox_uint32(v_a_55_);
lean_dec(v_a_55_);
v_res_60_ = l_OverflowLoop___redArg___lam__2(v_toApplicative_52_, v___x_53_, v_toBind_54_, v_a_boxed_59_, v_x_56_, v___y_57_, v___y_58_);
lean_dec(v___x_53_);
return v_res_60_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowLoop___redArg(mut v_inst1_61_: *mut lean_object, mut v_xs_62_: *mut lean_object, mut v_a_63_: *mut lean_object) -> *mut lean_object{
let mut v___f_64_: *mut lean_object = core::ptr::null_mut(); let mut v___f_65_: *mut lean_object = core::ptr::null_mut(); let mut v___f_66_: *mut lean_object = core::ptr::null_mut(); let mut v___f_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v_toApplicative_74_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_75_: *mut lean_object = core::ptr::null_mut(); let mut v___f_76_: *mut lean_object = core::ptr::null_mut(); let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v_out_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___f_80_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_81_: usize = 0; let mut v___x_82_: usize = 0; let mut v___x_581__overap_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref_n(v_inst1_61_, 7);
v___f_64_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_64_, 0, v_inst1_61_);
v___f_65_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_65_, 0, v_inst1_61_);
v___f_66_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_66_, 0, v_inst1_61_);
v___f_67_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_67_, 0, v_inst1_61_);
v___x_68_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_68_, 0, lean_box(0));
lean_closure_set(v___x_68_, 1, lean_box(0));
lean_closure_set(v___x_68_, 2, v_inst1_61_);
v___x_69_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___f_64_);
v___x_70_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
lean_closure_set(v___x_70_, 0, lean_box(0));
lean_closure_set(v___x_70_, 1, lean_box(0));
lean_closure_set(v___x_70_, 2, v_inst1_61_);
v___x_71_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
lean_ctor_set(v___x_71_, 2, v___f_65_);
lean_ctor_set(v___x_71_, 3, v___f_66_);
lean_ctor_set(v___x_71_, 4, v___f_67_);
v___x_72_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_72_, 0, lean_box(0));
lean_closure_set(v___x_72_, 1, lean_box(0));
lean_closure_set(v___x_72_, 2, v_inst1_61_);
v___x_73_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v_toApplicative_74_ = lean_ctor_get(v_inst1_61_, 0);
lean_inc_ref_n(v_toApplicative_74_, 2);
v_toBind_75_ = lean_ctor_get(v_inst1_61_, 1);
lean_inc_n(v_toBind_75_, 2);
lean_dec_ref(v_inst1_61_);
v___f_76_ = lean_alloc_closure(l_OverflowLoop___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_76_, 0, v_toApplicative_74_);
v___x_77_ = lean_box(0);
v_out_78_ = lean_unsigned_to_nat(0);
lean_inc_ref(v___x_73_);
v___x_79_ = l_instInhabitedOfMonad___redArg(v___x_73_, v___x_77_);
v___f_80_ = lean_alloc_closure(l_OverflowLoop___redArg___lam__2___boxed as *mut core::ffi::c_void, 7, 3);
lean_closure_set(v___f_80_, 0, v_toApplicative_74_);
lean_closure_set(v___f_80_, 1, v___x_79_);
lean_closure_set(v___f_80_, 2, v_toBind_75_);
v_sz_81_ = lean_array_size(v_xs_62_);
v___x_82_ = 0usize;
v___x_581__overap_83_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_73_, v_xs_62_, v___f_80_, v_sz_81_, v___x_82_, v_out_78_);
v___x_84_ = lean_apply_1(v___x_581__overap_83_, v_a_63_);
v___x_85_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_84_, v___f_76_);
return v___x_85_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowLoop(mut v_m_86_: *mut lean_object, mut v_inst1_87_: *mut lean_object, mut v_xs_88_: *mut lean_object, mut v_a_89_: *mut lean_object) -> *mut lean_object{
let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); 
v___x_90_ = l_OverflowLoop___redArg(v_inst1_87_, v_xs_88_, v_a_89_);
return v___x_90_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(mut v_s_91_: *mut lean_object) -> *mut lean_object{
let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); 
v___x_93_ = lean_get_stdout();
v_putStr_94_ = lean_ctor_get(v___x_93_, 4);
lean_inc_ref(v_putStr_94_);
lean_dec_ref(v___x_93_);
v___x_95_ = lean_apply_2(v_putStr_94_, v_s_91_, lean_box(0));
return v___x_95_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__3___boxed(mut v_s_96_: *mut lean_object, mut v_a_97_: *mut lean_object) -> *mut lean_object{
let mut v_res_98_: *mut lean_object = core::ptr::null_mut(); 
v_res_98_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(v_s_96_);
return v_res_98_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_99_: *mut lean_object) -> *mut lean_object{
let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: u32 = 0; let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); 
v___x_101_ = l_Nat_reprFast(v_s_99_);
v___x_102_ = 10;
v___x_103_ = lean_string_push(v___x_101_, v___x_102_);
v___x_104_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(v___x_103_);
return v___x_104_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_105_: *mut lean_object, mut v_a_106_: *mut lean_object) -> *mut lean_object{
let mut v_res_107_: *mut lean_object = core::ptr::null_mut(); 
v_res_107_ = l_IO_println___at___00main_spec__1(v_s_105_);
return v_res_107_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0(mut v_msg_115_: *mut lean_object, mut v___y_116_: *mut lean_object) -> *mut lean_object{
let mut v___f_117_: *mut lean_object = core::ptr::null_mut(); let mut v___f_118_: *mut lean_object = core::ptr::null_mut(); let mut v___f_119_: *mut lean_object = core::ptr::null_mut(); let mut v___f_120_: *mut lean_object = core::ptr::null_mut(); let mut v___f_121_: *mut lean_object = core::ptr::null_mut(); let mut v___f_122_: *mut lean_object = core::ptr::null_mut(); let mut v___f_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___f_127_: *mut lean_object = core::ptr::null_mut(); let mut v___f_128_: *mut lean_object = core::ptr::null_mut(); let mut v___f_129_: *mut lean_object = core::ptr::null_mut(); let mut v___f_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_332__overap_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); 
v___f_117_ = l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__0;
v___f_118_ = l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__1;
v___f_119_ = l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__2;
v___f_120_ = l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__3;
v___f_121_ = l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__4;
v___f_122_ = l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__5;
v___f_123_ = l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0___closed__6;
v___x_124_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_124_, 0, v___f_117_);
lean_ctor_set(v___x_124_, 1, v___f_118_);
v___x_125_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___f_119_);
lean_ctor_set(v___x_125_, 2, v___f_120_);
lean_ctor_set(v___x_125_, 3, v___f_121_);
lean_ctor_set(v___x_125_, 4, v___f_122_);
v___x_126_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___f_123_);
lean_inc_ref_n(v___x_126_, 6);
v___f_127_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_127_, 0, v___x_126_);
v___f_128_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_128_, 0, v___x_126_);
v___f_129_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_129_, 0, v___x_126_);
v___f_130_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_130_, 0, v___x_126_);
v___x_131_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_131_, 0, lean_box(0));
lean_closure_set(v___x_131_, 1, lean_box(0));
lean_closure_set(v___x_131_, 2, v___x_126_);
v___x_132_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___f_127_);
v___x_133_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
lean_closure_set(v___x_133_, 0, lean_box(0));
lean_closure_set(v___x_133_, 1, lean_box(0));
lean_closure_set(v___x_133_, 2, v___x_126_);
v___x_134_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
lean_ctor_set(v___x_134_, 2, v___f_128_);
lean_ctor_set(v___x_134_, 3, v___f_129_);
lean_ctor_set(v___x_134_, 4, v___f_130_);
v___x_135_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_135_, 0, lean_box(0));
lean_closure_set(v___x_135_, 1, lean_box(0));
lean_closure_set(v___x_135_, 2, v___x_126_);
v___x_136_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_box(0);
v___x_138_ = l_instInhabitedOfMonad___redArg(v___x_136_, v___x_137_);
v___x_332__overap_139_ = lean_panic_fn_borrowed(v___x_138_, v_msg_115_);
lean_dec(v___x_138_);
v___x_140_ = lean_apply_1(v___x_332__overap_139_, v___y_116_);
return v___x_140_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00OverflowLoop___at___00main_spec__0_spec__1(mut v_as_141_: *mut lean_object, mut v_sz_142_: usize, mut v_i_143_: usize, mut v_b_144_: *mut lean_object, mut v___y_145_: *mut lean_object) -> *mut lean_object{
let mut v_a_147_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: usize = 0; let mut v___x_150_: usize = 0; let mut v___x_152_: u8 = 0; let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v_a_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: u32 = 0; let mut v___x_156_: u32 = 0; let mut v___x_157_: u8 = 0; let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_162_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_152_ = lean_usize_dec_lt(v_i_143_, v_sz_142_);
if v___x_152_ == 0 {
let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); 
v___x_153_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_153_, 0, v_b_144_);
lean_ctor_set(v___x_153_, 1, v___y_145_);
return v___x_153_;
} else {
let mut v_a_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: u32 = 0; let mut v___x_156_: u32 = 0; let mut v___x_157_: u8 = 0; 
v_a_154_ = lean_array_uget_borrowed(v_as_141_, v_i_143_);
v___x_155_ = 122;
v___x_156_ = lean_unbox_uint32(v_a_154_);
v___x_157_ = lean_uint32_dec_eq(v___x_156_, v___x_155_);
if v___x_157_ == 0 {
let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); 
v___x_158_ = lean_unsigned_to_nat(1);
v___x_159_ = lean_nat_add(v_b_144_, v___x_158_);
lean_dec(v_b_144_);
v_a_147_ = v___x_159_;
v_snd_148_ = v___y_145_;
state = 1; continue;
} else {
let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_162_: *mut lean_object = core::ptr::null_mut(); 
v___x_160_ = l_OverflowLoop___redArg___lam__2___closed__0;
v___x_161_ = l_panic___at___00OverflowLoop___at___00main_spec__0_spec__0(v___x_160_, v___y_145_);
v_snd_162_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_snd_162_);
lean_dec_ref(v___x_161_);
v_a_147_ = v_b_144_;
v_snd_148_ = v_snd_162_;
state = 1; continue;
}
}
}
1 => {
v___x_149_ = 1usize;
v___x_150_ = lean_usize_add(v_i_143_, v___x_149_);
v_i_143_ = v___x_150_;
v_b_144_ = v_a_147_;
v___y_145_ = v_snd_148_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00OverflowLoop___at___00main_spec__0_spec__1___boxed(mut v_as_163_: *mut lean_object, mut v_sz_164_: *mut lean_object, mut v_i_165_: *mut lean_object, mut v_b_166_: *mut lean_object, mut v___y_167_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_168_: usize = 0; let mut v_i_boxed_169_: usize = 0; let mut v_res_170_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_168_ = lean_unbox_usize(v_sz_164_);
lean_dec(v_sz_164_);
v_i_boxed_169_ = lean_unbox_usize(v_i_165_);
lean_dec(v_i_165_);
v_res_170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00OverflowLoop___at___00main_spec__0_spec__1(v_as_163_, v_sz_boxed_168_, v_i_boxed_169_, v_b_166_, v___y_167_);
lean_dec_ref(v_as_163_);
return v_res_170_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowLoop___at___00main_spec__0(mut v_xs_171_: *mut lean_object, mut v_a_172_: *mut lean_object) -> *mut lean_object{
let mut v_out_173_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_174_: usize = 0; let mut v___x_175_: usize = 0; let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); 
v_out_173_ = lean_unsigned_to_nat(0);
v_sz_174_ = lean_array_size(v_xs_171_);
v___x_175_ = 0usize;
v___x_176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00OverflowLoop___at___00main_spec__0_spec__1(v_xs_171_, v_sz_174_, v___x_175_, v_out_173_, v_a_172_);
return v___x_176_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowLoop___at___00main_spec__0___boxed(mut v_xs_177_: *mut lean_object, mut v_a_178_: *mut lean_object) -> *mut lean_object{
let mut v_res_179_: *mut lean_object = core::ptr::null_mut(); 
v_res_179_ = l_OverflowLoop___at___00main_spec__0(v_xs_177_, v_a_178_);
lean_dec_ref(v_xs_177_);
return v_res_179_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); 
v___x_182_ = l_main___closed__0;
v___x_183_ = lean_unsigned_to_nat(50000);
v___x_184_ = l_longArray(v___x_183_, v___x_182_);
return v___x_184_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); let mut v___x_186_: *mut lean_object = core::ptr::null_mut(); let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); 
v___x_185_ = lean_unsigned_to_nat(0);
v___x_186_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_187_ = l_OverflowLoop___at___00main_spec__0(v___x_186_, v___x_185_);
return v___x_187_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); 
v___x_189_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v_fst_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_fst_190_);
v___x_191_ = l_IO_println___at___00main_spec__1(v_fst_190_);
return v___x_191_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_192_: *mut lean_object) -> *mut lean_object{
let mut v_res_193_: *mut lean_object = core::ptr::null_mut(); 
v_res_193_ = _lean_main();
return v_res_193_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_overflow3(builtin: u8) -> *mut lean_object {
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
  let res = initialize_overflow3(1 /* builtin */);
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
