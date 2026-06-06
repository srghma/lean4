// Lean compiler output
// Module: reusebug
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Int_repr(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_to_int(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_Expr_Expr_toString___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Expr_Expr_toString___closed__0: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_Expr_toString___closed__1_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 43, 32, 0]};
static mut l_Expr_Expr_toString___closed__1: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_Expr_toString___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Expr_Expr_toString___closed__2: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_Expr_toString___closed__3_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 42, 32, 0]};
static mut l_Expr_Expr_toString___closed__3: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_instToString___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Expr_Expr_toString___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Expr_instToString___closed__0: *mut lean_object = core::ptr::addr_of!(l_Expr_instToString___closed__0_value) as *mut lean_object;
#[no_mangle] pub static mut l_Expr_instToString: *mut lean_object = core::ptr::addr_of!(l_Expr_instToString___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_main___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l_main___redArg___closed__0_value) as *mut lean_object] };
static mut l_main___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__1_value) as *mut lean_object;
static mut l_main___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__7: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__8: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_main___redArg___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorIdx(mut v_x_1_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_1_)
{
0 => {
let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); 
v___x_2_ = lean_unsigned_to_nat(0);
return v___x_2_;
}
1 => {
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_unsigned_to_nat(1);
return v___x_3_;
}
2 => {
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = lean_unsigned_to_nat(2);
return v___x_4_;
}
_ => {
let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_5_ = lean_unsigned_to_nat(3);
return v___x_5_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorIdx___boxed(mut v_x_6_: *mut lean_object) -> *mut lean_object{
let mut v_res_7_: *mut lean_object = core::ptr::null_mut(); 
v_res_7_ = l_Expr_ctorIdx(v_x_6_);
lean_dec_ref(v_x_6_);
return v_res_7_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorElim___redArg(mut v_t_8_: *mut lean_object, mut v_k_9_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_t_8_)
{
0 => {
let mut v_a_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); 
v_a_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v_t_8_, 1);
v___x_11_ = lean_apply_1(v_k_9_, v_a_10_);
return v___x_11_;
}
1 => {
let mut v_a_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v_a_12_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_a_12_);
lean_dec_ref_known(v_t_8_, 1);
v___x_13_ = lean_apply_1(v_k_9_, v_a_12_);
return v___x_13_;
}
_ => {
let mut v_a_14_: *mut lean_object = core::ptr::null_mut(); let mut v_a_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); 
v_a_14_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_a_14_);
v_a_15_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_a_15_);
lean_dec_ref(v_t_8_);
v___x_16_ = lean_apply_2(v_k_9_, v_a_14_, v_a_15_);
return v___x_16_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorElim(mut v_motive_17_: *mut lean_object, mut v_ctorIdx_18_: *mut lean_object, mut v_t_19_: *mut lean_object, mut v_h_20_: *mut lean_object, mut v_k_21_: *mut lean_object) -> *mut lean_object{
let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); 
v___x_22_ = l_Expr_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorElim___boxed(mut v_motive_23_: *mut lean_object, mut v_ctorIdx_24_: *mut lean_object, mut v_t_25_: *mut lean_object, mut v_h_26_: *mut lean_object, mut v_k_27_: *mut lean_object) -> *mut lean_object{
let mut v_res_28_: *mut lean_object = core::ptr::null_mut(); 
v_res_28_ = l_Expr_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Val_elim___redArg(mut v_t_29_: *mut lean_object, mut v_Val_30_: *mut lean_object) -> *mut lean_object{
let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); 
v___x_31_ = l_Expr_ctorElim___redArg(v_t_29_, v_Val_30_);
return v___x_31_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Val_elim(mut v_motive_32_: *mut lean_object, mut v_t_33_: *mut lean_object, mut v_h_34_: *mut lean_object, mut v_Val_35_: *mut lean_object) -> *mut lean_object{
let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); 
v___x_36_ = l_Expr_ctorElim___redArg(v_t_33_, v_Val_35_);
return v___x_36_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Var_elim___redArg(mut v_t_37_: *mut lean_object, mut v_Var_38_: *mut lean_object) -> *mut lean_object{
let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); 
v___x_39_ = l_Expr_ctorElim___redArg(v_t_37_, v_Var_38_);
return v___x_39_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Var_elim(mut v_motive_40_: *mut lean_object, mut v_t_41_: *mut lean_object, mut v_h_42_: *mut lean_object, mut v_Var_43_: *mut lean_object) -> *mut lean_object{
let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
v___x_44_ = l_Expr_ctorElim___redArg(v_t_41_, v_Var_43_);
return v___x_44_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Add_elim___redArg(mut v_t_45_: *mut lean_object, mut v_Add_46_: *mut lean_object) -> *mut lean_object{
let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); 
v___x_47_ = l_Expr_ctorElim___redArg(v_t_45_, v_Add_46_);
return v___x_47_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Add_elim(mut v_motive_48_: *mut lean_object, mut v_t_49_: *mut lean_object, mut v_h_50_: *mut lean_object, mut v_Add_51_: *mut lean_object) -> *mut lean_object{
let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); 
v___x_52_ = l_Expr_ctorElim___redArg(v_t_49_, v_Add_51_);
return v___x_52_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Mul_elim___redArg(mut v_t_53_: *mut lean_object, mut v_Mul_54_: *mut lean_object) -> *mut lean_object{
let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); 
v___x_55_ = l_Expr_ctorElim___redArg(v_t_53_, v_Mul_54_);
return v___x_55_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Mul_elim(mut v_motive_56_: *mut lean_object, mut v_t_57_: *mut lean_object, mut v_h_58_: *mut lean_object, mut v_Mul_59_: *mut lean_object) -> *mut lean_object{
let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); 
v___x_60_ = l_Expr_ctorElim___redArg(v_t_57_, v_Mul_59_);
return v___x_60_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Expr_toString(mut v_x_65_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_65_)
{
0 => {
let mut v_a_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v_a_66_ = lean_ctor_get(v_x_65_, 0);
v___x_67_ = l_Int_repr(v_a_66_);
return v___x_67_;
}
1 => {
let mut v_a_68_: *mut lean_object = core::ptr::null_mut(); 
v_a_68_ = lean_ctor_get(v_x_65_, 0);
lean_inc_ref(v_a_68_);
return v_a_68_;
}
2 => {
let mut v_a_69_: *mut lean_object = core::ptr::null_mut(); let mut v_a_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); 
v_a_69_ = lean_ctor_get(v_x_65_, 0);
v_a_70_ = lean_ctor_get(v_x_65_, 1);
v___x_71_ = l_Expr_Expr_toString___closed__0;
v___x_72_ = l_Expr_Expr_toString(v_a_69_);
v___x_73_ = lean_string_append(v___x_71_, v___x_72_);
lean_dec_ref(v___x_72_);
v___x_74_ = l_Expr_Expr_toString___closed__1;
v___x_75_ = lean_string_append(v___x_73_, v___x_74_);
v___x_76_ = l_Expr_Expr_toString(v_a_70_);
v___x_77_ = lean_string_append(v___x_75_, v___x_76_);
lean_dec_ref(v___x_76_);
v___x_78_ = l_Expr_Expr_toString___closed__2;
v___x_79_ = lean_string_append(v___x_77_, v___x_78_);
return v___x_79_;
}
_ => {
let mut v_a_80_: *mut lean_object = core::ptr::null_mut(); let mut v_a_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); 
v_a_80_ = lean_ctor_get(v_x_65_, 0);
v_a_81_ = lean_ctor_get(v_x_65_, 1);
v___x_82_ = l_Expr_Expr_toString___closed__0;
v___x_83_ = l_Expr_Expr_toString(v_a_80_);
v___x_84_ = lean_string_append(v___x_82_, v___x_83_);
lean_dec_ref(v___x_83_);
v___x_85_ = l_Expr_Expr_toString___closed__3;
v___x_86_ = lean_string_append(v___x_84_, v___x_85_);
v___x_87_ = l_Expr_Expr_toString(v_a_81_);
v___x_88_ = lean_string_append(v___x_86_, v___x_87_);
lean_dec_ref(v___x_87_);
v___x_89_ = l_Expr_Expr_toString___closed__2;
v___x_90_ = lean_string_append(v___x_88_, v___x_89_);
return v___x_90_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Expr_toString___boxed(mut v_x_91_: *mut lean_object) -> *mut lean_object{
let mut v_res_92_: *mut lean_object = core::ptr::null_mut(); 
v_res_92_ = l_Expr_Expr_toString(v_x_91_);
lean_dec_ref(v_x_91_);
return v_res_92_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_addAux(mut v_x_95_: *mut lean_object, mut v_x_96_: *mut lean_object) -> *mut lean_object{
let mut v_a_97_: *mut lean_object = core::ptr::null_mut(); let mut v_a_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_96_) == 2 {
let mut v_a_97_: *mut lean_object = core::ptr::null_mut(); 
v_a_97_ = lean_ctor_get(v_x_96_, 0);
if lean_obj_tag(v_a_97_) == 0 {
let mut v_a_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_97_);
v_a_98_ = lean_ctor_get(v_x_96_, 1);
lean_inc_ref(v_a_98_);
lean_dec_ref_known(v_x_96_, 2);
v___x_99_ = l_Expr_addAux(v_x_95_, v_a_98_);
v_x_95_ = v_a_97_;
v_x_96_ = v___x_99_;
state = 0; continue;
} else {
let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); 
v___x_101_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_101_, 0, v_x_95_);
lean_ctor_set(v___x_101_, 1, v_x_96_);
return v___x_101_;
}
} else {
let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
v___x_102_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_102_, 0, v_x_95_);
lean_ctor_set(v___x_102_, 1, v_x_96_);
return v___x_102_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_add(mut v_a_103_: *mut lean_object, mut v_b_104_: *mut lean_object) -> *mut lean_object{
let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); 
v___x_105_ = l_Expr_addAux(v_a_103_, v_b_104_);
return v___x_105_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_106_: *mut lean_object) -> *mut lean_object{
let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); 
v___x_108_ = lean_get_stdout();
v_putStr_109_ = lean_ctor_get(v___x_108_, 4);
lean_inc_ref(v_putStr_109_);
lean_dec_ref(v___x_108_);
v___x_110_ = lean_apply_2(v_putStr_109_, v_s_106_, lean_box(0));
return v___x_110_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_111_: *mut lean_object, mut v_a_112_: *mut lean_object) -> *mut lean_object{
let mut v_res_113_: *mut lean_object = core::ptr::null_mut(); 
v_res_113_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_111_);
return v_res_113_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_114_: *mut lean_object) -> *mut lean_object{
let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: u32 = 0; let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); 
v___x_116_ = l_Expr_Expr_toString(v_s_114_);
v___x_117_ = 10;
v___x_118_ = lean_string_push(v___x_116_, v___x_117_);
v___x_119_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_118_);
return v___x_119_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_120_: *mut lean_object, mut v_a_121_: *mut lean_object) -> *mut lean_object{
let mut v_res_122_: *mut lean_object = core::ptr::null_mut(); 
v_res_122_ = l_IO_println___at___00main_spec__0(v_s_120_);
lean_dec_ref(v_s_120_);
return v_res_122_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__2() -> *mut lean_object{
let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); 
v___x_126_ = lean_unsigned_to_nat(1);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__3() -> *mut lean_object{
let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); 
v___x_128_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__2), core::ptr::addr_of_mut!(l_main___redArg___closed__2_once), _init_l_main___redArg___closed__2);
v___x_129_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__4() -> *mut lean_object{
let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); 
v___x_130_ = lean_unsigned_to_nat(2);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__5() -> *mut lean_object{
let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); 
v___x_132_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__4), core::ptr::addr_of_mut!(l_main___redArg___closed__4_once), _init_l_main___redArg___closed__4);
v___x_133_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__6() -> *mut lean_object{
let mut v_x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); 
v_x_134_ = l_main___redArg___closed__1;
v___x_135_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__5), core::ptr::addr_of_mut!(l_main___redArg___closed__5_once), _init_l_main___redArg___closed__5);
v___x_136_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v_x_134_);
return v___x_136_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__7() -> *mut lean_object{
let mut v_x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); 
v_x_137_ = l_main___redArg___closed__1;
v___x_138_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__6), core::ptr::addr_of_mut!(l_main___redArg___closed__6_once), _init_l_main___redArg___closed__6);
v___x_139_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_x_137_);
return v___x_139_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__8() -> *mut lean_object{
let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); 
v___x_140_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__7), core::ptr::addr_of_mut!(l_main___redArg___closed__7_once), _init_l_main___redArg___closed__7);
v___x_141_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__3), core::ptr::addr_of_mut!(l_main___redArg___closed__3_once), _init_l_main___redArg___closed__3);
v___x_142_ = l_Expr_addAux(v___x_141_, v___x_140_);
return v___x_142_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___boxed__const__1() -> *mut lean_object{
let mut v___x_143_: u32 = 0; let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); 
v___x_143_ = 0;
v___x_144_ = lean_box_uint32(v___x_143_);
return v___x_144_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_150_: u8 = 0; let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_154_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_155_: u8 = 0; let mut v_unused_156_: *mut lean_object = core::ptr::null_mut(); let mut v_a_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_160_: u8 = 0; let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_163_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_164_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_146_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__8), core::ptr::addr_of_mut!(l_main___redArg___closed__8_once), _init_l_main___redArg___closed__8);
v___x_147_ = l_IO_println___at___00main_spec__0(v___x_146_);
if lean_obj_tag(v___x_147_) == 0 {
let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_150_: u8 = 0; let mut v_isSharedCheck_155_: u8 = 0; 
v_isSharedCheck_155_ = (!lean_is_exclusive(v___x_147_)) as u8;
if v_isSharedCheck_155_ == 0 {
let mut v_unused_156_: *mut lean_object = core::ptr::null_mut(); 
v_unused_156_ = lean_ctor_get(v___x_147_, 0);
lean_dec(v_unused_156_);
v___x_149_ = v___x_147_;
v_isShared_150_ = v_isSharedCheck_155_;
state = 1; continue;
} else {
lean_dec(v___x_147_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
state = 1; continue;
}
} else {
let mut v_a_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_160_: u8 = 0; let mut v_isSharedCheck_164_: u8 = 0; 
v_a_157_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_164_ = (!lean_is_exclusive(v___x_147_)) as u8;
if v_isSharedCheck_164_ == 0 {
v___x_159_ = v___x_147_;
v_isShared_160_ = v_isSharedCheck_164_;
state = 3; continue;
} else {
lean_inc(v_a_157_);
lean_dec(v___x_147_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
state = 3; continue;
}
}
}
1 => {
v___x_151_ = l_main___redArg___boxed__const__1;
if v_isShared_150_ == 0 {
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_154_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
state = 2; continue;
}
}
3 => {
if v_isShared_160_ == 0 {
v___x_162_ = v___x_159_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_163_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_165_: *mut lean_object) -> *mut lean_object{
let mut v_res_166_: *mut lean_object = core::ptr::null_mut(); 
v_res_166_ = l_main___redArg();
return v_res_166_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_167_: *mut lean_object) -> *mut lean_object{
let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_xs_167_);
v___x_169_ = l_main___redArg();
return v___x_169_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_170_: *mut lean_object, mut v_a_171_: *mut lean_object) -> *mut lean_object{
let mut v_res_172_: *mut lean_object = core::ptr::null_mut(); 
v_res_172_ = _lean_main(v_xs_170_);
return v_res_172_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_reusebug(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_main___redArg___boxed__const__1 = _init_l_main___redArg___boxed__const__1();
lean_mark_persistent(l_main___redArg___boxed__const__1);
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
  let res = initialize_reusebug(1 /* builtin */);
  lean_io_mark_end_initialization();
  let mut ret_val = 1;
  if lean_io_result_is_ok(res) {
    lean_dec(res);
    lean_init_task_manager();
    let main_res = lean_run_main(run_main, argc, argv);
    lean_finalize_task_manager();
    if lean_io_result_is_ok(main_res) {
      ret_val = lean_unbox_uint32(lean_io_result_get_value(main_res)) as i32;
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
