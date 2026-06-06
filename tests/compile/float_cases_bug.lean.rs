// Lean compiler output
// Module: float_cases_bug
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn l_List_reverse___redArg(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_Term_instInhabited___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_Term_instInhabited___closed__0: *mut lean_object = core::ptr::addr_of!(l_Term_instInhabited___closed__0_value) as *mut lean_object;
#[no_mangle] pub static mut l_Term_instInhabited: *mut lean_object = core::ptr::addr_of!(l_Term_instInhabited___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Term_hasToString___closed__0_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [67, 79, 78, 83, 84, 40, 0]};
static mut l_Term_hasToString___closed__0: *mut lean_object = core::ptr::addr_of!(l_Term_hasToString___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Term_hasToString___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Term_hasToString___closed__1: *mut lean_object = core::ptr::addr_of!(l_Term_hasToString___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_Term_hasToString___closed__2_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 80, 80, 0]};
static mut l_Term_hasToString___closed__2: *mut lean_object = core::ptr::addr_of!(l_Term_hasToString___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_Term_instToString___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Term_hasToString as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Term_instToString___closed__0: *mut lean_object = core::ptr::addr_of!(l_Term_instToString___closed__0_value) as *mut lean_object;
#[no_mangle] pub static mut l_Term_instToString: *mut lean_object = core::ptr::addr_of!(l_Term_instToString___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_foo___redArg___lam__0___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut lean_object] };
static mut l_foo___redArg___lam__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_foo___redArg___lam__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_foo___redArg___lam__0___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_foo___redArg___lam__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_foo___redArg___lam__0___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_foo___redArg___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_foo___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_foo___redArg___closed__0_value) as *mut lean_object;
static mut l_foo___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_foo___redArg___closed__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__0_spec__0_spec__1___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__0_spec__0_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__0_spec__0_spec__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__2_value) as *mut lean_object;
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_Term_ctorIdx(mut v_x_1_: *mut lean_object) -> *mut lean_object{
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
#[no_mangle] pub unsafe extern "C" fn l_Term_ctorIdx___boxed(mut v_x_4_: *mut lean_object) -> *mut lean_object{
let mut v_res_5_: *mut lean_object = core::ptr::null_mut(); 
v_res_5_ = l_Term_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_Term_ctorElim___redArg(mut v_t_6_: *mut lean_object, mut v_k_7_: *mut lean_object) -> *mut lean_object{
let mut v_a_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); 
v_a_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_a_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_a_8_);
return v___x_9_;
}
#[no_mangle] pub unsafe extern "C" fn l_Term_ctorElim(mut v_motive__1_10_: *mut lean_object, mut v_ctorIdx_11_: *mut lean_object, mut v_t_12_: *mut lean_object, mut v_h_13_: *mut lean_object, mut v_k_14_: *mut lean_object) -> *mut lean_object{
let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_15_ = l_Term_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_Term_ctorElim___boxed(mut v_motive__1_16_: *mut lean_object, mut v_ctorIdx_17_: *mut lean_object, mut v_t_18_: *mut lean_object, mut v_h_19_: *mut lean_object, mut v_k_20_: *mut lean_object) -> *mut lean_object{
let mut v_res_21_: *mut lean_object = core::ptr::null_mut(); 
v_res_21_ = l_Term_ctorElim(v_motive__1_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
#[no_mangle] pub unsafe extern "C" fn l_Term_const_elim___redArg(mut v_t_22_: *mut lean_object, mut v_const_23_: *mut lean_object) -> *mut lean_object{
let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); 
v___x_24_ = l_Term_ctorElim___redArg(v_t_22_, v_const_23_);
return v___x_24_;
}
#[no_mangle] pub unsafe extern "C" fn l_Term_const_elim(mut v_motive__1_25_: *mut lean_object, mut v_t_26_: *mut lean_object, mut v_h_27_: *mut lean_object, mut v_const_28_: *mut lean_object) -> *mut lean_object{
let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); 
v___x_29_ = l_Term_ctorElim___redArg(v_t_26_, v_const_28_);
return v___x_29_;
}
#[no_mangle] pub unsafe extern "C" fn l_Term_app_elim___redArg(mut v_t_30_: *mut lean_object, mut v_app_31_: *mut lean_object) -> *mut lean_object{
let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
v___x_32_ = l_Term_ctorElim___redArg(v_t_30_, v_app_31_);
return v___x_32_;
}
#[no_mangle] pub unsafe extern "C" fn l_Term_app_elim(mut v_motive__1_33_: *mut lean_object, mut v_t_34_: *mut lean_object, mut v_h_35_: *mut lean_object, mut v_app_36_: *mut lean_object) -> *mut lean_object{
let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
v___x_37_ = l_Term_ctorElim___redArg(v_t_34_, v_app_36_);
return v___x_37_;
}
#[no_mangle] pub unsafe extern "C" fn l_Term_hasToString(mut v_x_44_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_44_) == 0 {
let mut v_a_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); 
v_a_45_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v_x_44_, 1);
v___x_46_ = l_Term_hasToString___closed__0;
v___x_47_ = l_Nat_reprFast(v_a_45_);
v___x_48_ = lean_string_append(v___x_46_, v___x_47_);
lean_dec_ref(v___x_47_);
v___x_49_ = l_Term_hasToString___closed__1;
v___x_50_ = lean_string_append(v___x_48_, v___x_49_);
return v___x_50_;
} else {
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_44_, 1);
v___x_51_ = l_Term_hasToString___closed__2;
return v___x_51_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_emit(mut v_t_54_: *mut lean_object, mut v_a_55_: *mut lean_object) -> *mut lean_object{
let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); 
v___x_56_ = lean_box(0);
v___x_57_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_57_, 0, v_t_54_);
lean_ctor_set(v___x_57_, 1, v_a_55_);
v___x_58_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
return v___x_58_;
}
#[no_mangle] pub unsafe extern "C" fn l_foo___redArg___lam__0(mut v_x_63_: *mut lean_object, mut v_x_64_: *mut lean_object, mut v_____r_65_: *mut lean_object, mut v___y_66_: *mut lean_object) -> *mut lean_object{
let mut v___y_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___y_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_77_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_63_) == 1 {
if lean_obj_tag(v_x_64_) == 1 {
let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_77_: *mut lean_object = core::ptr::null_mut(); 
v___x_75_ = l_foo___redArg___lam__0___closed__1;
v___x_76_ = l_emit(v___x_75_, v___y_66_);
v_snd_77_ = lean_ctor_get(v___x_76_, 1);
lean_inc(v_snd_77_);
lean_dec_ref(v___x_76_);
v___y_72_ = v_snd_77_;
state = 2; continue;
} else {
v___y_72_ = v___y_66_;
state = 2; continue;
}
} else {
v___y_72_ = v___y_66_;
state = 2; continue;
}
}
1 => {
v___x_69_ = l_foo___redArg___lam__0___closed__0;
v___x_70_ = l_emit(v___x_69_, v___y_68_);
return v___x_70_;
}
2 => {
if lean_obj_tag(v_x_63_) == 1 {
if lean_obj_tag(v_x_64_) == 1 {
let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); 
v___x_73_ = l_foo___redArg___lam__0___closed__1;
v___x_74_ = l_emit(v___x_73_, v___y_72_);
return v___x_74_;
} else {
v___y_68_ = v___y_72_;
state = 1; continue;
}
} else {
v___y_68_ = v___y_72_;
state = 1; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_foo___redArg___lam__0___boxed(mut v_x_78_: *mut lean_object, mut v_x_79_: *mut lean_object, mut v_____r_80_: *mut lean_object, mut v___y_81_: *mut lean_object) -> *mut lean_object{
let mut v_res_82_: *mut lean_object = core::ptr::null_mut(); 
v_res_82_ = l_foo___redArg___lam__0(v_x_78_, v_x_79_, v_____r_80_, v___y_81_);
lean_dec_ref(v_x_79_);
lean_dec_ref(v_x_78_);
return v_res_82_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_foo___redArg___closed__1() -> *mut lean_object{
let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); 
v___x_85_ = lean_box(0);
v___x_86_ = l_foo___redArg___closed__0;
v___x_87_ = l_emit(v___x_86_, v___x_85_);
return v___x_87_;
}
#[no_mangle] pub unsafe extern "C" fn l_foo___redArg(mut v_x_88_: *mut lean_object, mut v_x_89_: *mut lean_object) -> *mut lean_object{
let mut v___y_91_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_98_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_94_ = lean_box(0);
if lean_obj_tag(v_x_88_) == 0 {
let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); 
v___x_95_ = lean_box(0);
v___x_96_ = l_foo___redArg___lam__0(v_x_88_, v_x_89_, v___x_95_, v___x_94_);
v___y_91_ = v___x_96_;
state = 1; continue;
} else {
let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_98_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); 
v___x_97_ = lean_obj_once(core::ptr::addr_of_mut!(l_foo___redArg___closed__1), core::ptr::addr_of_mut!(l_foo___redArg___closed__1_once), _init_l_foo___redArg___closed__1);
v_fst_98_ = lean_ctor_get(v___x_97_, 0);
v_snd_99_ = lean_ctor_get(v___x_97_, 1);
lean_inc(v_snd_99_);
lean_inc(v_fst_98_);
v___x_100_ = l_foo___redArg___lam__0(v_x_88_, v_x_89_, v_fst_98_, v_snd_99_);
v___y_91_ = v___x_100_;
state = 1; continue;
}
}
1 => {
v_snd_92_ = lean_ctor_get(v___y_91_, 1);
lean_inc(v_snd_92_);
lean_dec_ref(v___y_91_);
v___x_93_ = l_List_reverse___redArg(v_snd_92_);
return v___x_93_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_foo___redArg___boxed(mut v_x_101_: *mut lean_object, mut v_x_102_: *mut lean_object) -> *mut lean_object{
let mut v_res_103_: *mut lean_object = core::ptr::null_mut(); 
v_res_103_ = l_foo___redArg(v_x_101_, v_x_102_);
lean_dec_ref(v_x_102_);
lean_dec_ref(v_x_101_);
return v_res_103_;
}
#[no_mangle] pub unsafe extern "C" fn l_foo(mut v_x_104_: *mut lean_object, mut v_x_105_: *mut lean_object, mut v_x_106_: *mut lean_object) -> *mut lean_object{
let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); 
v___x_107_ = l_foo___redArg(v_x_105_, v_x_106_);
return v___x_107_;
}
#[no_mangle] pub unsafe extern "C" fn l_foo___boxed(mut v_x_108_: *mut lean_object, mut v_x_109_: *mut lean_object, mut v_x_110_: *mut lean_object) -> *mut lean_object{
let mut v_res_111_: *mut lean_object = core::ptr::null_mut(); 
v_res_111_ = l_foo(v_x_108_, v_x_109_, v_x_110_);
lean_dec_ref(v_x_110_);
lean_dec_ref(v_x_109_);
lean_dec(v_x_108_);
return v_res_111_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__1(mut v_s_112_: *mut lean_object) -> *mut lean_object{
let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); 
v___x_114_ = lean_get_stdout();
v_putStr_115_ = lean_ctor_get(v___x_114_, 4);
lean_inc_ref(v_putStr_115_);
lean_dec_ref(v___x_114_);
v___x_116_ = lean_apply_2(v_putStr_115_, v_s_112_, lean_box(0));
return v___x_116_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__1___boxed(mut v_s_117_: *mut lean_object, mut v_a_118_: *mut lean_object) -> *mut lean_object{
let mut v_res_119_: *mut lean_object = core::ptr::null_mut(); 
v_res_119_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__1(v_s_117_);
return v_res_119_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__0_spec__0_spec__1(mut v_x_121_: *mut lean_object, mut v_x_122_: *mut lean_object) -> *mut lean_object{
let mut v_head_123_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_122_) == 0 {
return v_x_121_;
} else {
let mut v_head_123_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); 
v_head_123_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_head_123_);
v_tail_124_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_tail_124_);
lean_dec_ref_known(v_x_122_, 2);
v___x_125_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__0_spec__0_spec__1___closed__0;
v___x_126_ = lean_string_append(v_x_121_, v___x_125_);
v___x_127_ = l_Term_hasToString(v_head_123_);
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
lean_dec_ref(v___x_127_);
v_x_121_ = v___x_128_;
v_x_122_ = v_tail_124_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00main_spec__0_spec__0(mut v_x_133_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_133_) == 0 {
let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); 
v___x_134_ = l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__0;
return v___x_134_;
} else {
let mut v_tail_135_: *mut lean_object = core::ptr::null_mut(); 
v_tail_135_ = lean_ctor_get(v_x_133_, 1);
if lean_obj_tag(v_tail_135_) == 0 {
let mut v_head_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); 
v_head_136_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_head_136_);
lean_dec_ref_known(v_x_133_, 2);
v___x_137_ = l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__1;
v___x_138_ = l_Term_hasToString(v_head_136_);
v___x_139_ = lean_string_append(v___x_137_, v___x_138_);
lean_dec_ref(v___x_138_);
v___x_140_ = l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__2;
v___x_141_ = lean_string_append(v___x_139_, v___x_140_);
return v___x_141_;
} else {
let mut v_head_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: u32 = 0; let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_tail_135_);
v_head_142_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_head_142_);
lean_dec_ref_known(v_x_133_, 2);
v___x_143_ = l_List_toString___at___00IO_println___at___00main_spec__0_spec__0___closed__1;
v___x_144_ = l_Term_hasToString(v_head_142_);
v___x_145_ = lean_string_append(v___x_143_, v___x_144_);
lean_dec_ref(v___x_144_);
v___x_146_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__0_spec__0_spec__1(v___x_145_, v_tail_135_);
v___x_147_ = 93;
v___x_148_ = lean_string_push(v___x_146_, v___x_147_);
return v___x_148_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_149_: *mut lean_object) -> *mut lean_object{
let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: u32 = 0; let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); 
v___x_151_ = l_List_toString___at___00IO_println___at___00main_spec__0_spec__0(v_s_149_);
v___x_152_ = 10;
v___x_153_ = lean_string_push(v___x_151_, v___x_152_);
v___x_154_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__1(v___x_153_);
return v___x_154_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_155_: *mut lean_object, mut v_a_156_: *mut lean_object) -> *mut lean_object{
let mut v_res_157_: *mut lean_object = core::ptr::null_mut(); 
v_res_157_ = l_IO_println___at___00main_spec__0(v_s_155_);
return v_res_157_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); 
v___x_158_ = l_foo___redArg___lam__0___closed__1;
v___x_159_ = l_foo___redArg(v___x_158_, v___x_158_);
return v___x_159_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); 
v___x_161_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_162_ = l_IO_println___at___00main_spec__0(v___x_161_);
return v___x_162_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_163_: *mut lean_object) -> *mut lean_object{
let mut v_res_164_: *mut lean_object = core::ptr::null_mut(); 
v_res_164_ = _lean_main();
return v_res_164_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_float__cases__bug(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_float__cases__bug(1 /* builtin */);
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
