// Lean compiler output
// Module: overflow1
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Control::Id::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::Data::Array::Basic::*;
use lean_init::Init::Control::State::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Bootstrap::*;
extern "C" {
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_panic_fn_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
}
#[used]
#[no_mangle]
pub static mut l_longArray___boxed__const__1: *mut lean_object = core::ptr::null_mut();
pub static l_OverflowIte___redArg___lam__0___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [122, 0]};
static mut l_OverflowIte___redArg___lam__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_OverflowIte___redArg___lam__0___closed__0_value) as *mut lean_object;
pub static l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__0_value) as *mut lean_object;
pub static l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__1_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__1_value) as *mut lean_object;
pub static l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__2_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__2: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__2_value) as *mut lean_object;
pub static l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__3_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__3: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__3_value) as *mut lean_object;
pub static l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__4_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__4: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__4_value) as *mut lean_object;
pub static l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__5_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__5: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__5_value) as *mut lean_object;
pub static l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__6_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__6: *mut lean_object = core::ptr::addr_of!(l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__6_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
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
#[no_mangle] pub unsafe extern "C" fn l_OverflowIte___redArg___lam__0(mut v_inst1_13_: *mut lean_object, mut v___x_14_: *mut lean_object, mut v_len_15_: *mut lean_object, mut v_s_16_: u32, mut v___y_17_: *mut lean_object) -> *mut lean_object{
let mut v___x_18_: u32 = 0; let mut v___x_19_: u8 = 0; let mut v_toApplicative_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_23_: u8 = 0; let mut v_toPure_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_30_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_31_: u8 = 0; let mut v_unused_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428__overap_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_18_ = 122;
v___x_19_ = lean_uint32_dec_eq(v_s_16_, v___x_18_);
if v___x_19_ == 0 {
lean_dec_ref(v___x_14_);
v_toApplicative_20_ = lean_ctor_get(v_inst1_13_, 0);
v_isSharedCheck_31_ = (!lean_is_exclusive(v_inst1_13_)) as u8;
if v_isSharedCheck_31_ == 0 {
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
lean_dec_ref(v_inst1_13_);
v___x_33_ = lean_unsigned_to_nat(0);
v___x_34_ = l_instInhabitedOfMonad___redArg(v___x_14_, v___x_33_);
v___x_35_ = l_OverflowIte___redArg___lam__0___closed__0;
v___x_428__overap_36_ = l_panic___redArg(v___x_34_, v___x_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_apply_1(v___x_428__overap_36_, v___y_17_);
return v___x_37_;
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
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___y_17_);
v___x_28_ = v_reuseFailAlloc_30_;
state = 2; continue;
}
}
2 => {
v___x_29_ = lean_apply_2(v_toPure_24_, lean_box(0), v___x_28_);
return v___x_29_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowIte___redArg___lam__0___boxed(mut v_inst1_38_: *mut lean_object, mut v___x_39_: *mut lean_object, mut v_len_40_: *mut lean_object, mut v_s_41_: *mut lean_object, mut v___y_42_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_43_: u32 = 0; let mut v_res_44_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_43_ = lean_unbox_uint32(v_s_41_);
lean_dec(v_s_41_);
v_res_44_ = l_OverflowIte___redArg___lam__0(v_inst1_38_, v___x_39_, v_len_40_, v_s_boxed_43_, v___y_42_);
lean_dec(v_len_40_);
return v_res_44_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowIte___redArg(mut v_inst1_45_: *mut lean_object, mut v_xs_46_: *mut lean_object, mut v_a_47_: *mut lean_object) -> *mut lean_object{
let mut v___f_48_: *mut lean_object = core::ptr::null_mut(); let mut v___f_49_: *mut lean_object = core::ptr::null_mut(); let mut v___f_50_: *mut lean_object = core::ptr::null_mut(); let mut v___f_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: u8 = 0; let mut v_toApplicative_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_64_: u8 = 0; let mut v_toPure_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_69_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_70_: u8 = 0; let mut v_unused_71_: *mut lean_object = core::ptr::null_mut(); let mut v___f_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: u8 = 0; let mut v_toApplicative_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_77_: u8 = 0; let mut v_toPure_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_82_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_83_: u8 = 0; let mut v_unused_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: usize = 0; let mut v___x_86_: usize = 0; let mut v___x_387__overap_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: usize = 0; let mut v___x_90_: usize = 0; let mut v___x_392__overap_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
lean_inc_ref_n(v_inst1_45_, 7);
v___f_48_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_48_, 0, v_inst1_45_);
v___f_49_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_49_, 0, v_inst1_45_);
v___f_50_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_50_, 0, v_inst1_45_);
v___f_51_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_51_, 0, v_inst1_45_);
v___x_52_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_52_, 0, lean_box(0));
lean_closure_set(v___x_52_, 1, lean_box(0));
lean_closure_set(v___x_52_, 2, v_inst1_45_);
v___x_53_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___f_48_);
v___x_54_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
lean_closure_set(v___x_54_, 0, lean_box(0));
lean_closure_set(v___x_54_, 1, lean_box(0));
lean_closure_set(v___x_54_, 2, v_inst1_45_);
v___x_55_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
lean_ctor_set(v___x_55_, 2, v___f_49_);
lean_ctor_set(v___x_55_, 3, v___f_50_);
lean_ctor_set(v___x_55_, 4, v___f_51_);
v___x_56_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_56_, 0, lean_box(0));
lean_closure_set(v___x_56_, 1, lean_box(0));
lean_closure_set(v___x_56_, 2, v_inst1_45_);
v___x_57_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_unsigned_to_nat(0);
v___x_59_ = lean_array_get_size(v_xs_46_);
v___x_60_ = lean_nat_dec_lt(v___x_58_, v___x_59_);
if v___x_60_ == 0 {
lean_dec_ref_known(v___x_57_, 2);
lean_dec_ref(v_xs_46_);
v_toApplicative_61_ = lean_ctor_get(v_inst1_45_, 0);
v_isSharedCheck_70_ = (!lean_is_exclusive(v_inst1_45_)) as u8;
if v_isSharedCheck_70_ == 0 {
v_unused_71_ = lean_ctor_get(v_inst1_45_, 1);
lean_dec(v_unused_71_);
v___x_63_ = v_inst1_45_;
v_isShared_64_ = v_isSharedCheck_70_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_61_);
lean_dec(v_inst1_45_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_70_;
state = 1; continue;
}
} else {
lean_inc_ref(v___x_57_);
lean_inc_ref(v_inst1_45_);
v___f_72_ = lean_alloc_closure(l_OverflowIte___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
lean_closure_set(v___f_72_, 0, v_inst1_45_);
lean_closure_set(v___f_72_, 1, v___x_57_);
v___x_73_ = lean_nat_dec_le(v___x_59_, v___x_59_);
if v___x_73_ == 0 {
if v___x_60_ == 0 {
lean_dec_ref(v___f_72_);
lean_dec_ref_known(v___x_57_, 2);
lean_dec_ref(v_xs_46_);
v_toApplicative_74_ = lean_ctor_get(v_inst1_45_, 0);
v_isSharedCheck_83_ = (!lean_is_exclusive(v_inst1_45_)) as u8;
if v_isSharedCheck_83_ == 0 {
v_unused_84_ = lean_ctor_get(v_inst1_45_, 1);
lean_dec(v_unused_84_);
v___x_76_ = v_inst1_45_;
v_isShared_77_ = v_isSharedCheck_83_;
state = 3; continue;
} else {
lean_inc(v_toApplicative_74_);
lean_dec(v_inst1_45_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_83_;
state = 3; continue;
}
} else {
lean_dec_ref(v_inst1_45_);
v___x_85_ = 0usize;
v___x_86_ = lean_usize_of_nat(v___x_59_);
v___x_387__overap_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_57_, v___f_72_, v_xs_46_, v___x_85_, v___x_86_, v___x_58_);
v___x_88_ = lean_apply_1(v___x_387__overap_87_, v_a_47_);
return v___x_88_;
}
} else {
lean_dec_ref(v_inst1_45_);
v___x_89_ = 0usize;
v___x_90_ = lean_usize_of_nat(v___x_59_);
v___x_392__overap_91_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_57_, v___f_72_, v_xs_46_, v___x_89_, v___x_90_, v___x_58_);
v___x_92_ = lean_apply_1(v___x_392__overap_91_, v_a_47_);
return v___x_92_;
}
}
}
1 => {
v_toPure_65_ = lean_ctor_get(v_toApplicative_61_, 1);
lean_inc(v_toPure_65_);
lean_dec_ref(v_toApplicative_61_);
if v_isShared_64_ == 0 {
lean_ctor_set(v___x_63_, 1, v_a_47_);
lean_ctor_set(v___x_63_, 0, v___x_58_);
v___x_67_ = v___x_63_;
state = 2; continue;
} else {
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_a_47_);
v___x_67_ = v_reuseFailAlloc_69_;
state = 2; continue;
}
}
2 => {
v___x_68_ = lean_apply_2(v_toPure_65_, lean_box(0), v___x_67_);
return v___x_68_;
}
3 => {
v_toPure_78_ = lean_ctor_get(v_toApplicative_74_, 1);
lean_inc(v_toPure_78_);
lean_dec_ref(v_toApplicative_74_);
if v_isShared_77_ == 0 {
lean_ctor_set(v___x_76_, 1, v_a_47_);
lean_ctor_set(v___x_76_, 0, v___x_58_);
v___x_80_ = v___x_76_;
state = 4; continue;
} else {
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_a_47_);
v___x_80_ = v_reuseFailAlloc_82_;
state = 4; continue;
}
}
4 => {
v___x_81_ = lean_apply_2(v_toPure_78_, lean_box(0), v___x_80_);
return v___x_81_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowIte(mut v_m_93_: *mut lean_object, mut v_inst1_94_: *mut lean_object, mut v_xs_95_: *mut lean_object, mut v_a_96_: *mut lean_object) -> *mut lean_object{
let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); 
v___x_97_ = l_OverflowIte___redArg(v_inst1_94_, v_xs_95_, v_a_96_);
return v___x_97_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(mut v_s_98_: *mut lean_object) -> *mut lean_object{
let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
v___x_100_ = lean_get_stdout();
v_putStr_101_ = lean_ctor_get(v___x_100_, 4);
lean_inc_ref(v_putStr_101_);
lean_dec_ref(v___x_100_);
v___x_102_ = lean_apply_2(v_putStr_101_, v_s_98_, lean_box(0));
return v___x_102_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__3___boxed(mut v_s_103_: *mut lean_object, mut v_a_104_: *mut lean_object) -> *mut lean_object{
let mut v_res_105_: *mut lean_object = core::ptr::null_mut(); 
v_res_105_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(v_s_103_);
return v_res_105_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_106_: *mut lean_object) -> *mut lean_object{
let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: u32 = 0; let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
v___x_108_ = l_Nat_reprFast(v_s_106_);
v___x_109_ = 10;
v___x_110_ = lean_string_push(v___x_108_, v___x_109_);
v___x_111_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(v___x_110_);
return v___x_111_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_112_: *mut lean_object, mut v_a_113_: *mut lean_object) -> *mut lean_object{
let mut v_res_114_: *mut lean_object = core::ptr::null_mut(); 
v_res_114_ = l_IO_println___at___00main_spec__1(v_s_112_);
return v_res_114_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00OverflowIte___at___00main_spec__0_spec__0(mut v_msg_122_: *mut lean_object, mut v___y_123_: *mut lean_object) -> *mut lean_object{
let mut v___f_124_: *mut lean_object = core::ptr::null_mut(); let mut v___f_125_: *mut lean_object = core::ptr::null_mut(); let mut v___f_126_: *mut lean_object = core::ptr::null_mut(); let mut v___f_127_: *mut lean_object = core::ptr::null_mut(); let mut v___f_128_: *mut lean_object = core::ptr::null_mut(); let mut v___f_129_: *mut lean_object = core::ptr::null_mut(); let mut v___f_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v___f_134_: *mut lean_object = core::ptr::null_mut(); let mut v___f_135_: *mut lean_object = core::ptr::null_mut(); let mut v___f_136_: *mut lean_object = core::ptr::null_mut(); let mut v___f_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254__overap_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); 
v___f_124_ = l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__0;
v___f_125_ = l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__1;
v___f_126_ = l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__2;
v___f_127_ = l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__3;
v___f_128_ = l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__4;
v___f_129_ = l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__5;
v___f_130_ = l_panic___at___00OverflowIte___at___00main_spec__0_spec__0___closed__6;
v___x_131_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_131_, 0, v___f_124_);
lean_ctor_set(v___x_131_, 1, v___f_125_);
v___x_132_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___f_126_);
lean_ctor_set(v___x_132_, 2, v___f_127_);
lean_ctor_set(v___x_132_, 3, v___f_128_);
lean_ctor_set(v___x_132_, 4, v___f_129_);
v___x_133_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___f_130_);
lean_inc_ref_n(v___x_133_, 6);
v___f_134_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_134_, 0, v___x_133_);
v___f_135_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_135_, 0, v___x_133_);
v___f_136_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_136_, 0, v___x_133_);
v___f_137_ = lean_alloc_closure(l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_137_, 0, v___x_133_);
v___x_138_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_138_, 0, lean_box(0));
lean_closure_set(v___x_138_, 1, lean_box(0));
lean_closure_set(v___x_138_, 2, v___x_133_);
v___x_139_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___f_134_);
v___x_140_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
lean_closure_set(v___x_140_, 0, lean_box(0));
lean_closure_set(v___x_140_, 1, lean_box(0));
lean_closure_set(v___x_140_, 2, v___x_133_);
v___x_141_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
lean_ctor_set(v___x_141_, 2, v___f_135_);
lean_ctor_set(v___x_141_, 3, v___f_136_);
lean_ctor_set(v___x_141_, 4, v___f_137_);
v___x_142_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_142_, 0, lean_box(0));
lean_closure_set(v___x_142_, 1, lean_box(0));
lean_closure_set(v___x_142_, 2, v___x_133_);
v___x_143_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_143_, 0, v___x_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(0);
v___x_145_ = l_instInhabitedOfMonad___redArg(v___x_143_, v___x_144_);
v___x_254__overap_146_ = lean_panic_fn_borrowed(v___x_145_, v_msg_122_);
lean_dec(v___x_145_);
v___x_147_ = lean_apply_1(v___x_254__overap_146_, v___y_123_);
return v___x_147_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowIte___at___00main_spec__0_spec__1(mut v_as_148_: *mut lean_object, mut v_i_149_: usize, mut v_stop_150_: usize, mut v_b_151_: *mut lean_object, mut v___y_152_: *mut lean_object) -> *mut lean_object{
let mut v_fst_154_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: usize = 0; let mut v___x_157_: usize = 0; let mut v___x_159_: u8 = 0; let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: u32 = 0; let mut v___x_162_: u32 = 0; let mut v___x_163_: u8 = 0; let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_168_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_159_ = lean_usize_dec_eq(v_i_149_, v_stop_150_);
if v___x_159_ == 0 {
v___x_160_ = lean_array_uget_borrowed(v_as_148_, v_i_149_);
v___x_161_ = 122;
v___x_162_ = lean_unbox_uint32(v___x_160_);
v___x_163_ = lean_uint32_dec_eq(v___x_162_, v___x_161_);
if v___x_163_ == 0 {
v___x_164_ = lean_unsigned_to_nat(1);
v___x_165_ = lean_nat_add(v_b_151_, v___x_164_);
lean_dec(v_b_151_);
v_fst_154_ = v___x_165_;
v_snd_155_ = v___y_152_;
state = 1; continue;
} else {
lean_dec(v_b_151_);
v___x_166_ = l_OverflowIte___redArg___lam__0___closed__0;
v___x_167_ = l_panic___at___00OverflowIte___at___00main_spec__0_spec__0(v___x_166_, v___y_152_);
v_fst_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_fst_168_);
v_snd_169_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_snd_169_);
lean_dec_ref(v___x_167_);
v_fst_154_ = v_fst_168_;
v_snd_155_ = v_snd_169_;
state = 1; continue;
}
} else {
v___x_170_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_170_, 0, v_b_151_);
lean_ctor_set(v___x_170_, 1, v___y_152_);
return v___x_170_;
}
}
1 => {
v___x_156_ = 1usize;
v___x_157_ = lean_usize_add(v_i_149_, v___x_156_);
v_i_149_ = v___x_157_;
v_b_151_ = v_fst_154_;
v___y_152_ = v_snd_155_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowIte___at___00main_spec__0_spec__1___boxed(mut v_as_171_: *mut lean_object, mut v_i_172_: *mut lean_object, mut v_stop_173_: *mut lean_object, mut v_b_174_: *mut lean_object, mut v___y_175_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_176_: usize = 0; let mut v_stop_boxed_177_: usize = 0; let mut v_res_178_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_176_ = lean_unbox_usize(v_i_172_);
lean_dec(v_i_172_);
v_stop_boxed_177_ = lean_unbox_usize(v_stop_173_);
lean_dec(v_stop_173_);
v_res_178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowIte___at___00main_spec__0_spec__1(v_as_171_, v_i_boxed_176_, v_stop_boxed_177_, v_b_174_, v___y_175_);
lean_dec_ref(v_as_171_);
return v_res_178_;
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowIte___at___00main_spec__0(mut v_xs_179_: *mut lean_object, mut v_a_180_: *mut lean_object) -> *mut lean_object{
let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_183_: u8 = 0; 
v___x_181_ = lean_unsigned_to_nat(0);
v___x_182_ = lean_array_get_size(v_xs_179_);
v___x_183_ = lean_nat_dec_lt(v___x_181_, v___x_182_);
if v___x_183_ == 0 {
let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); 
v___x_184_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v_a_180_);
return v___x_184_;
} else {
let mut v___x_185_: u8 = 0; 
v___x_185_ = lean_nat_dec_le(v___x_182_, v___x_182_);
if v___x_185_ == 0 {
if v___x_183_ == 0 {
let mut v___x_186_: *mut lean_object = core::ptr::null_mut(); 
v___x_186_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_186_, 0, v___x_181_);
lean_ctor_set(v___x_186_, 1, v_a_180_);
return v___x_186_;
} else {
let mut v___x_187_: usize = 0; let mut v___x_188_: usize = 0; let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); 
v___x_187_ = 0usize;
v___x_188_ = lean_usize_of_nat(v___x_182_);
v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowIte___at___00main_spec__0_spec__1(v_xs_179_, v___x_187_, v___x_188_, v___x_181_, v_a_180_);
return v___x_189_;
}
} else {
let mut v___x_190_: usize = 0; let mut v___x_191_: usize = 0; let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); 
v___x_190_ = 0usize;
v___x_191_ = lean_usize_of_nat(v___x_182_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00OverflowIte___at___00main_spec__0_spec__1(v_xs_179_, v___x_190_, v___x_191_, v___x_181_, v_a_180_);
return v___x_192_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_OverflowIte___at___00main_spec__0___boxed(mut v_xs_193_: *mut lean_object, mut v_a_194_: *mut lean_object) -> *mut lean_object{
let mut v_res_195_: *mut lean_object = core::ptr::null_mut(); 
v_res_195_ = l_OverflowIte___at___00main_spec__0(v_xs_193_, v_a_194_);
lean_dec_ref(v_xs_193_);
return v_res_195_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); 
v___x_198_ = l_main___closed__0;
v___x_199_ = lean_unsigned_to_nat(50000);
v___x_200_ = l_longArray(v___x_199_, v___x_198_);
return v___x_200_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); 
v___x_201_ = lean_unsigned_to_nat(0);
v___x_202_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_203_ = l_OverflowIte___at___00main_spec__0(v___x_202_, v___x_201_);
return v___x_203_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_206_: *mut lean_object = core::ptr::null_mut(); let mut v___x_207_: *mut lean_object = core::ptr::null_mut(); 
v___x_205_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v_fst_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_fst_206_);
v___x_207_ = l_IO_println___at___00main_spec__1(v_fst_206_);
return v___x_207_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_208_: *mut lean_object) -> *mut lean_object{
let mut v_res_209_: *mut lean_object = core::ptr::null_mut(); 
v_res_209_ = _lean_main();
return v_res_209_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_overflow1(builtin: u8) -> *mut lean_object {
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
  let res = initialize_overflow1(1 /* builtin */);
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
