// Lean compiler output
// Module: t4
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Int_repr(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_to_int(_: *mut lean_object) -> *mut lean_object;
    fn lean_int_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_int_ediv(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_int_mul(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_int_emod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_int_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_int_neg(_: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_Expr_Expr_toString___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Expr_Expr_toString___closed__0: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_Expr_toString___closed__1_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 43, 32, 0]};
static mut l_Expr_Expr_toString___closed__1: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_Expr_toString___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Expr_Expr_toString___closed__2: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_Expr_toString___closed__3_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 42, 32, 0]};
static mut l_Expr_Expr_toString___closed__3: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_Expr_toString___closed__4_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 94, 32, 0]};
static mut l_Expr_Expr_toString___closed__4: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_Expr_toString___closed__5_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 110, 40, 0]};
static mut l_Expr_Expr_toString___closed__5: *mut lean_object = core::ptr::addr_of!(l_Expr_Expr_toString___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_instToString___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Expr_Expr_toString___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Expr_instToString___closed__0: *mut lean_object = core::ptr::addr_of!(l_Expr_instToString___closed__0_value) as *mut lean_object;
#[no_mangle] pub static mut l_Expr_instToString: *mut lean_object = core::ptr::addr_of!(l_Expr_instToString___closed__0_value) as *mut lean_object;
static mut l_Expr_pown___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_pown___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_pown___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_pown___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_pown___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_pown___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_mulAux___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_mulAux___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_pow___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_pow___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_d___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_d___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_d___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_d___closed__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_Expr_deriv___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Expr_deriv___closed__0: *mut lean_object = core::ptr::addr_of!(l_Expr_deriv___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_deriv___closed__1_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [32, 99, 111, 117, 110, 116, 58, 32, 0]};
static mut l_Expr_deriv___closed__1: *mut lean_object = core::ptr::addr_of!(l_Expr_deriv___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l_Expr_deriv___closed__0_value) as *mut lean_object] };
static mut l_main___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__0_value) as *mut lean_object;
static mut l_main___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__4: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___redArg___closed__5_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Expr_deriv___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_main___redArg___closed__5: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__5_value) as *mut lean_object;
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
3 => {
let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_5_ = lean_unsigned_to_nat(3);
return v___x_5_;
}
4 => {
let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); 
v___x_6_ = lean_unsigned_to_nat(4);
return v___x_6_;
}
_ => {
let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); 
v___x_7_ = lean_unsigned_to_nat(5);
return v___x_7_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorIdx___boxed(mut v_x_8_: *mut lean_object) -> *mut lean_object{
let mut v_res_9_: *mut lean_object = core::ptr::null_mut(); 
v_res_9_ = l_Expr_ctorIdx(v_x_8_);
lean_dec_ref(v_x_8_);
return v_res_9_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorElim___redArg(mut v_t_10_: *mut lean_object, mut v_k_11_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_t_10_)
{
0 => {
let mut v_a_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v_a_12_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_a_12_);
lean_dec_ref_known(v_t_10_, 1);
v___x_13_ = lean_apply_1(v_k_11_, v_a_12_);
return v___x_13_;
}
1 => {
let mut v_a_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v_a_14_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_a_14_);
lean_dec_ref_known(v_t_10_, 1);
v___x_15_ = lean_apply_1(v_k_11_, v_a_14_);
return v___x_15_;
}
5 => {
let mut v_a_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); 
v_a_16_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_a_16_);
lean_dec_ref_known(v_t_10_, 1);
v___x_17_ = lean_apply_1(v_k_11_, v_a_16_);
return v___x_17_;
}
_ => {
let mut v_a_18_: *mut lean_object = core::ptr::null_mut(); let mut v_a_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); 
v_a_18_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_a_18_);
v_a_19_ = lean_ctor_get(v_t_10_, 1);
lean_inc_ref(v_a_19_);
lean_dec_ref(v_t_10_);
v___x_20_ = lean_apply_2(v_k_11_, v_a_18_, v_a_19_);
return v___x_20_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorElim(mut v_motive_21_: *mut lean_object, mut v_ctorIdx_22_: *mut lean_object, mut v_t_23_: *mut lean_object, mut v_h_24_: *mut lean_object, mut v_k_25_: *mut lean_object) -> *mut lean_object{
let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
v___x_26_ = l_Expr_ctorElim___redArg(v_t_23_, v_k_25_);
return v___x_26_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorElim___boxed(mut v_motive_27_: *mut lean_object, mut v_ctorIdx_28_: *mut lean_object, mut v_t_29_: *mut lean_object, mut v_h_30_: *mut lean_object, mut v_k_31_: *mut lean_object) -> *mut lean_object{
let mut v_res_32_: *mut lean_object = core::ptr::null_mut(); 
v_res_32_ = l_Expr_ctorElim(v_motive_27_, v_ctorIdx_28_, v_t_29_, v_h_30_, v_k_31_);
lean_dec(v_ctorIdx_28_);
return v_res_32_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Val_elim___redArg(mut v_t_33_: *mut lean_object, mut v_Val_34_: *mut lean_object) -> *mut lean_object{
let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); 
v___x_35_ = l_Expr_ctorElim___redArg(v_t_33_, v_Val_34_);
return v___x_35_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Val_elim(mut v_motive_36_: *mut lean_object, mut v_t_37_: *mut lean_object, mut v_h_38_: *mut lean_object, mut v_Val_39_: *mut lean_object) -> *mut lean_object{
let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_40_ = l_Expr_ctorElim___redArg(v_t_37_, v_Val_39_);
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Var_elim___redArg(mut v_t_41_: *mut lean_object, mut v_Var_42_: *mut lean_object) -> *mut lean_object{
let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); 
v___x_43_ = l_Expr_ctorElim___redArg(v_t_41_, v_Var_42_);
return v___x_43_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Var_elim(mut v_motive_44_: *mut lean_object, mut v_t_45_: *mut lean_object, mut v_h_46_: *mut lean_object, mut v_Var_47_: *mut lean_object) -> *mut lean_object{
let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); 
v___x_48_ = l_Expr_ctorElim___redArg(v_t_45_, v_Var_47_);
return v___x_48_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Add_elim___redArg(mut v_t_49_: *mut lean_object, mut v_Add_50_: *mut lean_object) -> *mut lean_object{
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
v___x_51_ = l_Expr_ctorElim___redArg(v_t_49_, v_Add_50_);
return v___x_51_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Add_elim(mut v_motive_52_: *mut lean_object, mut v_t_53_: *mut lean_object, mut v_h_54_: *mut lean_object, mut v_Add_55_: *mut lean_object) -> *mut lean_object{
let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); 
v___x_56_ = l_Expr_ctorElim___redArg(v_t_53_, v_Add_55_);
return v___x_56_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Mul_elim___redArg(mut v_t_57_: *mut lean_object, mut v_Mul_58_: *mut lean_object) -> *mut lean_object{
let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); 
v___x_59_ = l_Expr_ctorElim___redArg(v_t_57_, v_Mul_58_);
return v___x_59_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Mul_elim(mut v_motive_60_: *mut lean_object, mut v_t_61_: *mut lean_object, mut v_h_62_: *mut lean_object, mut v_Mul_63_: *mut lean_object) -> *mut lean_object{
let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); 
v___x_64_ = l_Expr_ctorElim___redArg(v_t_61_, v_Mul_63_);
return v___x_64_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Pow_elim___redArg(mut v_t_65_: *mut lean_object, mut v_Pow_66_: *mut lean_object) -> *mut lean_object{
let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v___x_67_ = l_Expr_ctorElim___redArg(v_t_65_, v_Pow_66_);
return v___x_67_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Pow_elim(mut v_motive_68_: *mut lean_object, mut v_t_69_: *mut lean_object, mut v_h_70_: *mut lean_object, mut v_Pow_71_: *mut lean_object) -> *mut lean_object{
let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); 
v___x_72_ = l_Expr_ctorElim___redArg(v_t_69_, v_Pow_71_);
return v___x_72_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Ln_elim___redArg(mut v_t_73_: *mut lean_object, mut v_Ln_74_: *mut lean_object) -> *mut lean_object{
let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); 
v___x_75_ = l_Expr_ctorElim___redArg(v_t_73_, v_Ln_74_);
return v___x_75_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Ln_elim(mut v_motive_76_: *mut lean_object, mut v_t_77_: *mut lean_object, mut v_h_78_: *mut lean_object, mut v_Ln_79_: *mut lean_object) -> *mut lean_object{
let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); 
v___x_80_ = l_Expr_ctorElim___redArg(v_t_77_, v_Ln_79_);
return v___x_80_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Expr_toString(mut v_x_87_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_87_)
{
0 => {
let mut v_a_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); 
v_a_88_ = lean_ctor_get(v_x_87_, 0);
v___x_89_ = l_Int_repr(v_a_88_);
return v___x_89_;
}
1 => {
let mut v_a_90_: *mut lean_object = core::ptr::null_mut(); 
v_a_90_ = lean_ctor_get(v_x_87_, 0);
lean_inc_ref(v_a_90_);
return v_a_90_;
}
2 => {
let mut v_a_91_: *mut lean_object = core::ptr::null_mut(); let mut v_a_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); 
v_a_91_ = lean_ctor_get(v_x_87_, 0);
v_a_92_ = lean_ctor_get(v_x_87_, 1);
v___x_93_ = l_Expr_Expr_toString___closed__0;
v___x_94_ = l_Expr_Expr_toString(v_a_91_);
v___x_95_ = lean_string_append(v___x_93_, v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = l_Expr_Expr_toString___closed__1;
v___x_97_ = lean_string_append(v___x_95_, v___x_96_);
v___x_98_ = l_Expr_Expr_toString(v_a_92_);
v___x_99_ = lean_string_append(v___x_97_, v___x_98_);
lean_dec_ref(v___x_98_);
v___x_100_ = l_Expr_Expr_toString___closed__2;
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
return v___x_101_;
}
3 => {
let mut v_a_102_: *mut lean_object = core::ptr::null_mut(); let mut v_a_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); 
v_a_102_ = lean_ctor_get(v_x_87_, 0);
v_a_103_ = lean_ctor_get(v_x_87_, 1);
v___x_104_ = l_Expr_Expr_toString___closed__0;
v___x_105_ = l_Expr_Expr_toString(v_a_102_);
v___x_106_ = lean_string_append(v___x_104_, v___x_105_);
lean_dec_ref(v___x_105_);
v___x_107_ = l_Expr_Expr_toString___closed__3;
v___x_108_ = lean_string_append(v___x_106_, v___x_107_);
v___x_109_ = l_Expr_Expr_toString(v_a_103_);
v___x_110_ = lean_string_append(v___x_108_, v___x_109_);
lean_dec_ref(v___x_109_);
v___x_111_ = l_Expr_Expr_toString___closed__2;
v___x_112_ = lean_string_append(v___x_110_, v___x_111_);
return v___x_112_;
}
4 => {
let mut v_a_113_: *mut lean_object = core::ptr::null_mut(); let mut v_a_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); 
v_a_113_ = lean_ctor_get(v_x_87_, 0);
v_a_114_ = lean_ctor_get(v_x_87_, 1);
v___x_115_ = l_Expr_Expr_toString___closed__0;
v___x_116_ = l_Expr_Expr_toString(v_a_113_);
v___x_117_ = lean_string_append(v___x_115_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = l_Expr_Expr_toString___closed__4;
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
v___x_120_ = l_Expr_Expr_toString(v_a_114_);
v___x_121_ = lean_string_append(v___x_119_, v___x_120_);
lean_dec_ref(v___x_120_);
v___x_122_ = l_Expr_Expr_toString___closed__2;
v___x_123_ = lean_string_append(v___x_121_, v___x_122_);
return v___x_123_;
}
_ => {
let mut v_a_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); 
v_a_124_ = lean_ctor_get(v_x_87_, 0);
v___x_125_ = l_Expr_Expr_toString___closed__5;
v___x_126_ = l_Expr_Expr_toString(v_a_124_);
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
lean_dec_ref(v___x_126_);
v___x_128_ = l_Expr_Expr_toString___closed__2;
v___x_129_ = lean_string_append(v___x_127_, v___x_128_);
return v___x_129_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Expr_toString___boxed(mut v_x_130_: *mut lean_object) -> *mut lean_object{
let mut v_res_131_: *mut lean_object = core::ptr::null_mut(); 
v_res_131_ = l_Expr_Expr_toString(v_x_130_);
lean_dec_ref(v_x_130_);
return v_res_131_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_pown___closed__0() -> *mut lean_object{
let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); 
v___x_134_ = lean_unsigned_to_nat(0);
v___x_135_ = lean_nat_to_int(v___x_134_);
return v___x_135_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_pown___closed__1() -> *mut lean_object{
let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); 
v___x_136_ = lean_unsigned_to_nat(1);
v___x_137_ = lean_nat_to_int(v___x_136_);
return v___x_137_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_pown___closed__2() -> *mut lean_object{
let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); 
v___x_138_ = lean_unsigned_to_nat(2);
v___x_139_ = lean_nat_to_int(v___x_138_);
return v___x_139_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_pown(mut v_x_140_: *mut lean_object, mut v_x_141_: *mut lean_object) -> *mut lean_object{
let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: u8 = 0; 
v___x_142_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_143_ = lean_int_dec_eq(v_x_141_, v___x_142_);
if v___x_143_ == 0 {
let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: u8 = 0; 
v___x_144_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_145_ = lean_int_dec_eq(v_x_141_, v___x_144_);
if v___x_145_ == 0 {
let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v_b_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: u8 = 0; 
v___x_146_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__2), core::ptr::addr_of_mut!(l_Expr_pown___closed__2_once), _init_l_Expr_pown___closed__2);
v___x_147_ = lean_int_ediv(v_x_141_, v___x_146_);
v_b_148_ = l_Expr_pown(v_x_140_, v___x_147_);
lean_dec(v___x_147_);
v___x_149_ = lean_int_mul(v_b_148_, v_b_148_);
lean_dec(v_b_148_);
v___x_150_ = lean_int_emod(v_x_141_, v___x_146_);
v___x_151_ = lean_int_dec_eq(v___x_150_, v___x_142_);
lean_dec(v___x_150_);
if v___x_151_ == 0 {
let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); 
v___x_152_ = lean_int_mul(v___x_149_, v_x_140_);
lean_dec(v___x_149_);
return v___x_152_;
} else {
let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); 
v___x_153_ = lean_int_mul(v___x_149_, v___x_144_);
lean_dec(v___x_149_);
return v___x_153_;
}
} else {
lean_inc(v_x_140_);
return v_x_140_;
}
} else {
let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); 
v___x_154_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
return v___x_154_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_pown___boxed(mut v_x_155_: *mut lean_object, mut v_x_156_: *mut lean_object) -> *mut lean_object{
let mut v_res_157_: *mut lean_object = core::ptr::null_mut(); 
v_res_157_ = l_Expr_pown(v_x_155_, v_x_156_);
lean_dec(v_x_156_);
lean_dec(v_x_155_);
return v_res_157_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_addAux(mut v_x_158_: *mut lean_object, mut v_x_159_: *mut lean_object) -> *mut lean_object{
let mut v_f_161_: *mut lean_object = core::ptr::null_mut(); let mut v_n_162_: *mut lean_object = core::ptr::null_mut(); let mut v_g_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v_f_168_: *mut lean_object = core::ptr::null_mut(); let mut v_n_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); let mut v_a_172_: *mut lean_object = core::ptr::null_mut(); let mut v_a_173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_176_: u8 = 0; let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_180_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_181_: u8 = 0; let mut v_a_182_: *mut lean_object = core::ptr::null_mut(); let mut v_a_183_: *mut lean_object = core::ptr::null_mut(); let mut v_a_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); let mut v___x_186_: u8 = 0; let mut v_a_187_: *mut lean_object = core::ptr::null_mut(); let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_190_: u8 = 0; let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_193_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_195_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_196_: u8 = 0; let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); let mut v_a_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: u8 = 0; let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v_a_202_: *mut lean_object = core::ptr::null_mut(); let mut v_a_203_: *mut lean_object = core::ptr::null_mut(); let mut v_h_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); let mut v_a_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: u8 = 0; let mut v_a_211_: *mut lean_object = core::ptr::null_mut(); let mut v_a_212_: *mut lean_object = core::ptr::null_mut(); let mut v_a_213_: *mut lean_object = core::ptr::null_mut(); let mut v_a_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: u8 = 0; let mut v_a_217_: *mut lean_object = core::ptr::null_mut(); let mut v_a_218_: *mut lean_object = core::ptr::null_mut(); let mut v_a_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_158_)
{
0 => {
match lean_obj_tag(v_x_159_)
{
0 => {
let mut v_a_172_: *mut lean_object = core::ptr::null_mut(); let mut v_a_173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_176_: u8 = 0; let mut v_isSharedCheck_181_: u8 = 0; 
v_a_172_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v_x_158_, 1);
v_a_173_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_181_ = (!lean_is_exclusive(v_x_159_)) as u8;
if v_isSharedCheck_181_ == 0 {
v___x_175_ = v_x_159_;
v_isShared_176_ = v_isSharedCheck_181_;
state = 3; continue;
} else {
lean_inc(v_a_173_);
lean_dec(v_x_159_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
state = 3; continue;
}
}
2 => {
let mut v_a_182_: *mut lean_object = core::ptr::null_mut(); let mut v_a_183_: *mut lean_object = core::ptr::null_mut(); let mut v_a_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); let mut v___x_186_: u8 = 0; 
v_a_182_ = lean_ctor_get(v_x_158_, 0);
v_a_183_ = lean_ctor_get(v_x_159_, 0);
lean_inc_ref(v_a_183_);
v_a_184_ = lean_ctor_get(v_x_159_, 1);
v___x_185_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_186_ = lean_int_dec_eq(v_a_182_, v___x_185_);
if v___x_186_ == 0 {
if lean_obj_tag(v_a_183_) == 0 {
let mut v_a_187_: *mut lean_object = core::ptr::null_mut(); let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_190_: u8 = 0; let mut v_isSharedCheck_196_: u8 = 0; 
lean_inc_ref(v_a_184_);
lean_inc(v_a_182_);
lean_dec_ref_known(v_x_159_, 2);
lean_dec_ref_known(v_x_158_, 1);
v_a_187_ = lean_ctor_get(v_a_183_, 0);
v_isSharedCheck_196_ = (!lean_is_exclusive(v_a_183_)) as u8;
if v_isSharedCheck_196_ == 0 {
v___x_189_ = v_a_183_;
v_isShared_190_ = v_isSharedCheck_196_;
state = 5; continue;
} else {
lean_inc(v_a_187_);
lean_dec(v_a_183_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_196_;
state = 5; continue;
}
} else {
let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_a_183_);
v___x_197_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_197_, 0, v_x_158_);
lean_ctor_set(v___x_197_, 1, v_x_159_);
return v___x_197_;
}
} else {
lean_dec_ref(v_a_183_);
lean_dec_ref_known(v_x_158_, 1);
return v_x_159_;
}
}
_ => {
let mut v_a_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: u8 = 0; 
v_a_198_ = lean_ctor_get(v_x_158_, 0);
v___x_199_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_200_ = lean_int_dec_eq(v_a_198_, v___x_199_);
if v___x_200_ == 0 {
let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); 
v___x_201_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_201_, 0, v_x_158_);
lean_ctor_set(v___x_201_, 1, v_x_159_);
return v___x_201_;
} else {
lean_dec_ref_known(v_x_158_, 1);
return v_x_159_;
}
}
}
}
2 => {
let mut v_a_202_: *mut lean_object = core::ptr::null_mut(); let mut v_a_203_: *mut lean_object = core::ptr::null_mut(); let mut v_h_205_: *mut lean_object = core::ptr::null_mut(); 
v_a_202_ = lean_ctor_get(v_x_158_, 0);
v_a_203_ = lean_ctor_get(v_x_158_, 1);
match lean_obj_tag(v_x_159_)
{
0 => {
let mut v_a_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: u8 = 0; 
v_a_208_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v_x_159_, 1);
v___x_209_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_210_ = lean_int_dec_eq(v_a_208_, v___x_209_);
if v___x_210_ == 0 {
v_f_168_ = v_x_158_;
v_n_169_ = v_a_208_;
state = 2; continue;
} else {
lean_dec(v_a_208_);
return v_x_158_;
}
}
2 => {
let mut v_a_211_: *mut lean_object = core::ptr::null_mut(); 
v_a_211_ = lean_ctor_get(v_x_159_, 0);
if lean_obj_tag(v_a_211_) == 0 {
let mut v_a_212_: *mut lean_object = core::ptr::null_mut(); let mut v_a_213_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_211_);
v_a_212_ = lean_ctor_get(v_x_159_, 1);
lean_inc_ref(v_a_212_);
lean_dec_ref_known(v_x_159_, 2);
v_a_213_ = lean_ctor_get(v_a_211_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v_a_211_, 1);
v_f_161_ = v_x_158_;
v_n_162_ = v_a_213_;
v_g_163_ = v_a_212_;
state = 1; continue;
} else {
lean_inc_ref(v_a_203_);
lean_inc_ref(v_a_202_);
lean_dec_ref_known(v_x_158_, 2);
v_h_205_ = v_x_159_;
state = 7; continue;
}
}
_ => {
lean_inc_ref(v_a_203_);
lean_inc_ref(v_a_202_);
lean_dec_ref_known(v_x_158_, 2);
v_h_205_ = v_x_159_;
state = 7; continue;
}
}
}
_ => {
match lean_obj_tag(v_x_159_)
{
0 => {
let mut v_a_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: u8 = 0; 
v_a_214_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v_x_159_, 1);
v___x_215_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_216_ = lean_int_dec_eq(v_a_214_, v___x_215_);
if v___x_216_ == 0 {
v_f_168_ = v_x_158_;
v_n_169_ = v_a_214_;
state = 2; continue;
} else {
lean_dec(v_a_214_);
return v_x_158_;
}
}
2 => {
let mut v_a_217_: *mut lean_object = core::ptr::null_mut(); 
v_a_217_ = lean_ctor_get(v_x_159_, 0);
if lean_obj_tag(v_a_217_) == 0 {
let mut v_a_218_: *mut lean_object = core::ptr::null_mut(); let mut v_a_219_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_217_);
v_a_218_ = lean_ctor_get(v_x_159_, 1);
lean_inc_ref(v_a_218_);
lean_dec_ref_known(v_x_159_, 2);
v_a_219_ = lean_ctor_get(v_a_217_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v_a_217_, 1);
v_f_161_ = v_x_158_;
v_n_162_ = v_a_219_;
v_g_163_ = v_a_218_;
state = 1; continue;
} else {
let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); 
v___x_220_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_220_, 0, v_x_158_);
lean_ctor_set(v___x_220_, 1, v_x_159_);
return v___x_220_;
}
}
_ => {
let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); 
v___x_221_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_221_, 0, v_x_158_);
lean_ctor_set(v___x_221_, 1, v_x_159_);
return v___x_221_;
}
}
}
}
}
1 => {
v___x_164_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_164_, 0, v_n_162_);
v___x_165_ = l_Expr_addAux(v_f_161_, v_g_163_);
v_x_158_ = v___x_164_;
v_x_159_ = v___x_165_;
state = 0; continue;
}
2 => {
v___x_170_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_170_, 0, v_n_169_);
v_x_158_ = v___x_170_;
v_x_159_ = v_f_168_;
state = 0; continue;
}
3 => {
v___x_177_ = lean_int_add(v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec(v_a_172_);
if v_isShared_176_ == 0 {
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_179_ = v___x_175_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_180_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
state = 4; continue;
}
}
5 => {
v___x_191_ = lean_int_add(v_a_182_, v_a_187_);
lean_dec(v_a_187_);
lean_dec(v_a_182_);
if v_isShared_190_ == 0 {
lean_ctor_set(v___x_189_, 0, v___x_191_);
v___x_193_ = v___x_189_;
state = 6; continue;
} else {
let mut v_reuseFailAlloc_195_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_195_;
state = 6; continue;
}
}
7 => {
v___x_206_ = l_Expr_addAux(v_a_203_, v_h_205_);
v_x_158_ = v_a_202_;
v_x_159_ = v___x_206_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_add(mut v_a_222_: *mut lean_object, mut v_b_223_: *mut lean_object) -> *mut lean_object{
let mut v___x_224_: *mut lean_object = core::ptr::null_mut(); 
v___x_224_ = l_Expr_addAux(v_a_222_, v_b_223_);
return v___x_224_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_mulAux___closed__0() -> *mut lean_object{
let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); 
v___x_225_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_226_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_mulAux(mut v_x_227_: *mut lean_object, mut v_x_228_: *mut lean_object) -> *mut lean_object{
let mut v_f_230_: *mut lean_object = core::ptr::null_mut(); let mut v_n_231_: *mut lean_object = core::ptr::null_mut(); let mut v_g_232_: *mut lean_object = core::ptr::null_mut(); let mut v___x_233_: *mut lean_object = core::ptr::null_mut(); let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v_f_237_: *mut lean_object = core::ptr::null_mut(); let mut v_n_238_: *mut lean_object = core::ptr::null_mut(); let mut v___x_239_: *mut lean_object = core::ptr::null_mut(); let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v_a_243_: *mut lean_object = core::ptr::null_mut(); let mut v_a_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_247_: u8 = 0; let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); let mut v___x_250_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_252_: u8 = 0; let mut v_a_253_: *mut lean_object = core::ptr::null_mut(); let mut v_a_254_: *mut lean_object = core::ptr::null_mut(); let mut v_a_255_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); let mut v___x_257_: u8 = 0; let mut v___x_258_: *mut lean_object = core::ptr::null_mut(); let mut v___x_259_: u8 = 0; let mut v_a_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_263_: u8 = 0; let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_268_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_269_: u8 = 0; let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v_a_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: u8 = 0; let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); let mut v___x_275_: u8 = 0; let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); let mut v_a_277_: *mut lean_object = core::ptr::null_mut(); let mut v_a_278_: *mut lean_object = core::ptr::null_mut(); let mut v_h_280_: *mut lean_object = core::ptr::null_mut(); let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v_a_283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_285_: u8 = 0; let mut v___x_286_: *mut lean_object = core::ptr::null_mut(); let mut v___x_287_: u8 = 0; let mut v_a_288_: *mut lean_object = core::ptr::null_mut(); let mut v_a_289_: *mut lean_object = core::ptr::null_mut(); let mut v_a_290_: *mut lean_object = core::ptr::null_mut(); let mut v_a_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: u8 = 0; let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); let mut v___x_295_: u8 = 0; let mut v_a_296_: *mut lean_object = core::ptr::null_mut(); let mut v_a_297_: *mut lean_object = core::ptr::null_mut(); let mut v_a_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_227_)
{
0 => {
match lean_obj_tag(v_x_228_)
{
0 => {
let mut v_a_243_: *mut lean_object = core::ptr::null_mut(); let mut v_a_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_247_: u8 = 0; let mut v_isSharedCheck_252_: u8 = 0; 
v_a_243_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v_x_227_, 1);
v_a_244_ = lean_ctor_get(v_x_228_, 0);
v_isSharedCheck_252_ = (!lean_is_exclusive(v_x_228_)) as u8;
if v_isSharedCheck_252_ == 0 {
v___x_246_ = v_x_228_;
v_isShared_247_ = v_isSharedCheck_252_;
state = 4; continue;
} else {
lean_inc(v_a_244_);
lean_dec(v_x_228_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
state = 4; continue;
}
}
3 => {
let mut v_a_253_: *mut lean_object = core::ptr::null_mut(); let mut v_a_254_: *mut lean_object = core::ptr::null_mut(); let mut v_a_255_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); let mut v___x_257_: u8 = 0; 
v_a_253_ = lean_ctor_get(v_x_227_, 0);
v_a_254_ = lean_ctor_get(v_x_228_, 0);
lean_inc_ref(v_a_254_);
v_a_255_ = lean_ctor_get(v_x_228_, 1);
v___x_256_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_257_ = lean_int_dec_eq(v_a_253_, v___x_256_);
if v___x_257_ == 0 {
let mut v___x_258_: *mut lean_object = core::ptr::null_mut(); let mut v___x_259_: u8 = 0; 
v___x_258_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_259_ = lean_int_dec_eq(v_a_253_, v___x_258_);
if v___x_259_ == 0 {
if lean_obj_tag(v_a_254_) == 0 {
let mut v_a_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_263_: u8 = 0; let mut v_isSharedCheck_269_: u8 = 0; 
lean_inc_ref(v_a_255_);
lean_inc(v_a_253_);
lean_dec_ref_known(v_x_228_, 2);
lean_dec_ref_known(v_x_227_, 1);
v_a_260_ = lean_ctor_get(v_a_254_, 0);
v_isSharedCheck_269_ = (!lean_is_exclusive(v_a_254_)) as u8;
if v_isSharedCheck_269_ == 0 {
v___x_262_ = v_a_254_;
v_isShared_263_ = v_isSharedCheck_269_;
state = 6; continue;
} else {
lean_inc(v_a_260_);
lean_dec(v_a_254_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_269_;
state = 6; continue;
}
} else {
let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_a_254_);
v___x_270_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_270_, 0, v_x_227_);
lean_ctor_set(v___x_270_, 1, v_x_228_);
return v___x_270_;
}
} else {
lean_dec_ref(v_a_254_);
lean_dec_ref_known(v_x_227_, 1);
return v_x_228_;
}
} else {
lean_dec_ref(v_a_254_);
lean_dec_ref_known(v_x_228_, 2);
lean_dec_ref_known(v_x_227_, 1);
state = 3; continue;
}
}
_ => {
let mut v_a_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: u8 = 0; 
v_a_271_ = lean_ctor_get(v_x_227_, 0);
v___x_272_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_273_ = lean_int_dec_eq(v_a_271_, v___x_272_);
if v___x_273_ == 0 {
let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); let mut v___x_275_: u8 = 0; 
v___x_274_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_275_ = lean_int_dec_eq(v_a_271_, v___x_274_);
if v___x_275_ == 0 {
let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); 
v___x_276_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_276_, 0, v_x_227_);
lean_ctor_set(v___x_276_, 1, v_x_228_);
return v___x_276_;
} else {
lean_dec_ref_known(v_x_227_, 1);
return v_x_228_;
}
} else {
lean_dec_ref_known(v_x_227_, 1);
lean_dec_ref(v_x_228_);
state = 3; continue;
}
}
}
}
3 => {
let mut v_a_277_: *mut lean_object = core::ptr::null_mut(); let mut v_a_278_: *mut lean_object = core::ptr::null_mut(); let mut v_h_280_: *mut lean_object = core::ptr::null_mut(); 
v_a_277_ = lean_ctor_get(v_x_227_, 0);
v_a_278_ = lean_ctor_get(v_x_227_, 1);
match lean_obj_tag(v_x_228_)
{
0 => {
let mut v_a_283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_285_: u8 = 0; 
v_a_283_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v_x_228_, 1);
v___x_284_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_285_ = lean_int_dec_eq(v_a_283_, v___x_284_);
if v___x_285_ == 0 {
let mut v___x_286_: *mut lean_object = core::ptr::null_mut(); let mut v___x_287_: u8 = 0; 
v___x_286_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_287_ = lean_int_dec_eq(v_a_283_, v___x_286_);
if v___x_287_ == 0 {
v_f_237_ = v_x_227_;
v_n_238_ = v_a_283_;
state = 2; continue;
} else {
lean_dec(v_a_283_);
return v_x_227_;
}
} else {
lean_dec(v_a_283_);
lean_dec_ref_known(v_x_227_, 2);
state = 3; continue;
}
}
3 => {
let mut v_a_288_: *mut lean_object = core::ptr::null_mut(); 
v_a_288_ = lean_ctor_get(v_x_228_, 0);
if lean_obj_tag(v_a_288_) == 0 {
let mut v_a_289_: *mut lean_object = core::ptr::null_mut(); let mut v_a_290_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_288_);
v_a_289_ = lean_ctor_get(v_x_228_, 1);
lean_inc_ref(v_a_289_);
lean_dec_ref_known(v_x_228_, 2);
v_a_290_ = lean_ctor_get(v_a_288_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v_a_288_, 1);
v_f_230_ = v_x_227_;
v_n_231_ = v_a_290_;
v_g_232_ = v_a_289_;
state = 1; continue;
} else {
lean_inc_ref(v_a_278_);
lean_inc_ref(v_a_277_);
lean_dec_ref_known(v_x_227_, 2);
v_h_280_ = v_x_228_;
state = 8; continue;
}
}
_ => {
lean_inc_ref(v_a_278_);
lean_inc_ref(v_a_277_);
lean_dec_ref_known(v_x_227_, 2);
v_h_280_ = v_x_228_;
state = 8; continue;
}
}
}
_ => {
match lean_obj_tag(v_x_228_)
{
0 => {
let mut v_a_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: u8 = 0; 
v_a_291_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v_x_228_, 1);
v___x_292_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_293_ = lean_int_dec_eq(v_a_291_, v___x_292_);
if v___x_293_ == 0 {
let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); let mut v___x_295_: u8 = 0; 
v___x_294_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_295_ = lean_int_dec_eq(v_a_291_, v___x_294_);
if v___x_295_ == 0 {
v_f_237_ = v_x_227_;
v_n_238_ = v_a_291_;
state = 2; continue;
} else {
lean_dec(v_a_291_);
return v_x_227_;
}
} else {
lean_dec(v_a_291_);
lean_dec_ref(v_x_227_);
state = 3; continue;
}
}
3 => {
let mut v_a_296_: *mut lean_object = core::ptr::null_mut(); 
v_a_296_ = lean_ctor_get(v_x_228_, 0);
if lean_obj_tag(v_a_296_) == 0 {
let mut v_a_297_: *mut lean_object = core::ptr::null_mut(); let mut v_a_298_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_296_);
v_a_297_ = lean_ctor_get(v_x_228_, 1);
lean_inc_ref(v_a_297_);
lean_dec_ref_known(v_x_228_, 2);
v_a_298_ = lean_ctor_get(v_a_296_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v_a_296_, 1);
v_f_230_ = v_x_227_;
v_n_231_ = v_a_298_;
v_g_232_ = v_a_297_;
state = 1; continue;
} else {
let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); 
v___x_299_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_299_, 0, v_x_227_);
lean_ctor_set(v___x_299_, 1, v_x_228_);
return v___x_299_;
}
}
_ => {
let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); 
v___x_300_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_300_, 0, v_x_227_);
lean_ctor_set(v___x_300_, 1, v_x_228_);
return v___x_300_;
}
}
}
}
}
1 => {
v___x_233_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_233_, 0, v_n_231_);
v___x_234_ = l_Expr_mulAux(v_f_230_, v_g_232_);
v_x_227_ = v___x_233_;
v_x_228_ = v___x_234_;
state = 0; continue;
}
2 => {
v___x_239_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_239_, 0, v_n_238_);
v_x_227_ = v___x_239_;
v_x_228_ = v_f_237_;
state = 0; continue;
}
3 => {
v___x_242_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0), core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0_once), _init_l_Expr_mulAux___closed__0);
return v___x_242_;
}
4 => {
v___x_248_ = lean_int_mul(v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec(v_a_243_);
if v_isShared_247_ == 0 {
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_251_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
state = 5; continue;
}
}
6 => {
v___x_264_ = lean_int_mul(v_a_253_, v_a_260_);
lean_dec(v_a_260_);
lean_dec(v_a_253_);
if v_isShared_263_ == 0 {
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_266_ = v___x_262_;
state = 7; continue;
} else {
let mut v_reuseFailAlloc_268_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_268_;
state = 7; continue;
}
}
8 => {
v___x_281_ = l_Expr_mulAux(v_a_278_, v_h_280_);
v_x_227_ = v_a_277_;
v_x_228_ = v___x_281_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_mul(mut v_a_301_: *mut lean_object, mut v_b_302_: *mut lean_object) -> *mut lean_object{
let mut v___x_303_: *mut lean_object = core::ptr::null_mut(); 
v___x_303_ = l_Expr_mulAux(v_a_301_, v_b_302_);
return v___x_303_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_pow___closed__0() -> *mut lean_object{
let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); 
v___x_304_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_305_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_pow(mut v_x_306_: *mut lean_object, mut v_x_307_: *mut lean_object) -> *mut lean_object{
let mut v_a_308_: *mut lean_object = core::ptr::null_mut(); let mut v_a_309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_312_: u8 = 0; let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_316_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_317_: u8 = 0; let mut v_a_318_: *mut lean_object = core::ptr::null_mut(); let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); let mut v___x_320_: u8 = 0; let mut v___x_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); let mut v_a_323_: *mut lean_object = core::ptr::null_mut(); let mut v___x_324_: *mut lean_object = core::ptr::null_mut(); let mut v___x_325_: u8 = 0; let mut v___x_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: u8 = 0; let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); let mut v___x_330_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_306_) == 0 {
if lean_obj_tag(v_x_307_) == 0 {
let mut v_a_308_: *mut lean_object = core::ptr::null_mut(); let mut v_a_309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_312_: u8 = 0; let mut v_isSharedCheck_317_: u8 = 0; 
v_a_308_ = lean_ctor_get(v_x_306_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v_x_306_, 1);
v_a_309_ = lean_ctor_get(v_x_307_, 0);
v_isSharedCheck_317_ = (!lean_is_exclusive(v_x_307_)) as u8;
if v_isSharedCheck_317_ == 0 {
v___x_311_ = v_x_307_;
v_isShared_312_ = v_isSharedCheck_317_;
state = 1; continue;
} else {
lean_inc(v_a_309_);
lean_dec(v_x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
state = 1; continue;
}
} else {
let mut v_a_318_: *mut lean_object = core::ptr::null_mut(); let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); let mut v___x_320_: u8 = 0; 
v_a_318_ = lean_ctor_get(v_x_306_, 0);
v___x_319_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_320_ = lean_int_dec_eq(v_a_318_, v___x_319_);
if v___x_320_ == 0 {
let mut v___x_321_: *mut lean_object = core::ptr::null_mut(); 
v___x_321_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_321_, 0, v_x_306_);
lean_ctor_set(v___x_321_, 1, v_x_307_);
return v___x_321_;
} else {
let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_306_, 1);
lean_dec_ref(v_x_307_);
v___x_322_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0), core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0_once), _init_l_Expr_mulAux___closed__0);
return v___x_322_;
}
}
} else {
if lean_obj_tag(v_x_307_) == 0 {
let mut v_a_323_: *mut lean_object = core::ptr::null_mut(); let mut v___x_324_: *mut lean_object = core::ptr::null_mut(); let mut v___x_325_: u8 = 0; 
v_a_323_ = lean_ctor_get(v_x_307_, 0);
v___x_324_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_325_ = lean_int_dec_eq(v_a_323_, v___x_324_);
if v___x_325_ == 0 {
let mut v___x_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: u8 = 0; 
v___x_326_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_327_ = lean_int_dec_eq(v_a_323_, v___x_326_);
if v___x_327_ == 0 {
let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); 
v___x_328_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_328_, 0, v_x_306_);
lean_ctor_set(v___x_328_, 1, v_x_307_);
return v___x_328_;
} else {
lean_dec_ref_known(v_x_307_, 1);
return v_x_306_;
}
} else {
let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_307_, 1);
lean_dec_ref(v_x_306_);
v___x_329_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pow___closed__0), core::ptr::addr_of_mut!(l_Expr_pow___closed__0_once), _init_l_Expr_pow___closed__0);
return v___x_329_;
}
} else {
let mut v___x_330_: *mut lean_object = core::ptr::null_mut(); 
v___x_330_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_330_, 0, v_x_306_);
lean_ctor_set(v___x_330_, 1, v_x_307_);
return v___x_330_;
}
}
}
1 => {
v___x_313_ = l_Expr_pown(v_a_308_, v_a_309_);
lean_dec(v_a_309_);
lean_dec(v_a_308_);
if v_isShared_312_ == 0 {
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_315_ = v___x_311_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_316_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ln(mut v_x_331_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_331_) == 0 {
let mut v_a_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: u8 = 0; 
v_a_332_ = lean_ctor_get(v_x_331_, 0);
v___x_333_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_334_ = lean_int_dec_eq(v_a_332_, v___x_333_);
if v___x_334_ == 0 {
let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); 
v___x_335_ = lean_alloc_ctor(5, 1, (0) as u32);
lean_ctor_set(v___x_335_, 0, v_x_331_);
return v___x_335_;
} else {
let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_331_, 1);
v___x_336_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0), core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0_once), _init_l_Expr_mulAux___closed__0);
return v___x_336_;
}
} else {
let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); 
v___x_337_ = lean_alloc_ctor(5, 1, (0) as u32);
lean_ctor_set(v___x_337_, 0, v_x_331_);
return v___x_337_;
}
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_d___closed__0() -> *mut lean_object{
let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: *mut lean_object = core::ptr::null_mut(); 
v___x_338_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_339_ = lean_int_neg(v___x_338_);
return v___x_339_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_d___closed__1() -> *mut lean_object{
let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); 
v___x_340_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_d___closed__0), core::ptr::addr_of_mut!(l_Expr_d___closed__0_once), _init_l_Expr_d___closed__0);
v___x_341_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_d(mut v_x_342_: *mut lean_object, mut v_x_343_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_343_)
{
0 => {
let mut v___x_344_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_343_, 1);
v___x_344_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0), core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0_once), _init_l_Expr_mulAux___closed__0);
return v___x_344_;
}
1 => {
let mut v_a_345_: *mut lean_object = core::ptr::null_mut(); let mut v___x_346_: u8 = 0; 
v_a_345_ = lean_ctor_get(v_x_343_, 0);
lean_inc_ref(v_a_345_);
lean_dec_ref_known(v_x_343_, 1);
v___x_346_ = lean_string_dec_eq(v_x_342_, v_a_345_);
lean_dec_ref(v_a_345_);
if v___x_346_ == 0 {
let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); 
v___x_347_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0), core::ptr::addr_of_mut!(l_Expr_mulAux___closed__0_once), _init_l_Expr_mulAux___closed__0);
return v___x_347_;
} else {
let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); 
v___x_348_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pow___closed__0), core::ptr::addr_of_mut!(l_Expr_pow___closed__0_once), _init_l_Expr_pow___closed__0);
return v___x_348_;
}
}
2 => {
let mut v_a_349_: *mut lean_object = core::ptr::null_mut(); let mut v_a_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_353_: *mut lean_object = core::ptr::null_mut(); 
v_a_349_ = lean_ctor_get(v_x_343_, 0);
lean_inc_ref(v_a_349_);
v_a_350_ = lean_ctor_get(v_x_343_, 1);
lean_inc_ref(v_a_350_);
lean_dec_ref_known(v_x_343_, 2);
v___x_351_ = l_Expr_d(v_x_342_, v_a_349_);
v___x_352_ = l_Expr_d(v_x_342_, v_a_350_);
v___x_353_ = l_Expr_addAux(v___x_351_, v___x_352_);
return v___x_353_;
}
3 => {
let mut v_a_354_: *mut lean_object = core::ptr::null_mut(); let mut v_a_355_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_357_: *mut lean_object = core::ptr::null_mut(); let mut v___x_358_: *mut lean_object = core::ptr::null_mut(); let mut v___x_359_: *mut lean_object = core::ptr::null_mut(); let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); 
v_a_354_ = lean_ctor_get(v_x_343_, 0);
lean_inc_ref_n(v_a_354_, 2);
v_a_355_ = lean_ctor_get(v_x_343_, 1);
lean_inc_ref_n(v_a_355_, 2);
lean_dec_ref_known(v_x_343_, 2);
v___x_356_ = l_Expr_d(v_x_342_, v_a_355_);
v___x_357_ = l_Expr_mulAux(v_a_354_, v___x_356_);
v___x_358_ = l_Expr_d(v_x_342_, v_a_354_);
v___x_359_ = l_Expr_mulAux(v_a_355_, v___x_358_);
v___x_360_ = l_Expr_addAux(v___x_357_, v___x_359_);
return v___x_360_;
}
4 => {
let mut v_a_361_: *mut lean_object = core::ptr::null_mut(); let mut v_a_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: *mut lean_object = core::ptr::null_mut(); let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); let mut v___x_365_: *mut lean_object = core::ptr::null_mut(); let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); let mut v___x_367_: *mut lean_object = core::ptr::null_mut(); let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); let mut v___x_372_: *mut lean_object = core::ptr::null_mut(); let mut v___x_373_: *mut lean_object = core::ptr::null_mut(); 
v_a_361_ = lean_ctor_get(v_x_343_, 0);
lean_inc_ref_n(v_a_361_, 4);
v_a_362_ = lean_ctor_get(v_x_343_, 1);
lean_inc_ref_n(v_a_362_, 3);
lean_dec_ref_known(v_x_343_, 2);
v___x_363_ = l_Expr_pow(v_a_361_, v_a_362_);
v___x_364_ = l_Expr_d(v_x_342_, v_a_361_);
v___x_365_ = l_Expr_mulAux(v_a_362_, v___x_364_);
v___x_366_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_d___closed__1), core::ptr::addr_of_mut!(l_Expr_d___closed__1_once), _init_l_Expr_d___closed__1);
v___x_367_ = l_Expr_pow(v_a_361_, v___x_366_);
v___x_368_ = l_Expr_mulAux(v___x_365_, v___x_367_);
v___x_369_ = l_Expr_ln(v_a_361_);
v___x_370_ = l_Expr_d(v_x_342_, v_a_362_);
v___x_371_ = l_Expr_mulAux(v___x_369_, v___x_370_);
v___x_372_ = l_Expr_addAux(v___x_368_, v___x_371_);
v___x_373_ = l_Expr_mulAux(v___x_363_, v___x_372_);
return v___x_373_;
}
_ => {
let mut v_a_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_375_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); 
v_a_374_ = lean_ctor_get(v_x_343_, 0);
lean_inc_ref_n(v_a_374_, 2);
lean_dec_ref_known(v_x_343_, 1);
v___x_375_ = l_Expr_d(v_x_342_, v_a_374_);
v___x_376_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_d___closed__1), core::ptr::addr_of_mut!(l_Expr_d___closed__1_once), _init_l_Expr_d___closed__1);
v___x_377_ = l_Expr_pow(v_a_374_, v___x_376_);
v___x_378_ = l_Expr_mulAux(v___x_375_, v___x_377_);
return v___x_378_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_d___boxed(mut v_x_379_: *mut lean_object, mut v_x_380_: *mut lean_object) -> *mut lean_object{
let mut v_res_381_: *mut lean_object = core::ptr::null_mut(); 
v_res_381_ = l_Expr_d(v_x_379_, v_x_380_);
lean_dec_ref(v_x_379_);
return v_res_381_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_count(mut v_x_382_: *mut lean_object) -> *mut lean_object{
let mut v_f_384_: *mut lean_object = core::ptr::null_mut(); let mut v_g_385_: *mut lean_object = core::ptr::null_mut(); let mut v___x_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: *mut lean_object = core::ptr::null_mut(); let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); let mut v_a_389_: *mut lean_object = core::ptr::null_mut(); let mut v_a_390_: *mut lean_object = core::ptr::null_mut(); let mut v_a_391_: *mut lean_object = core::ptr::null_mut(); let mut v_a_392_: *mut lean_object = core::ptr::null_mut(); let mut v_a_393_: *mut lean_object = core::ptr::null_mut(); let mut v_a_394_: *mut lean_object = core::ptr::null_mut(); let mut v_a_395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_397_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_382_)
{
2 => {
let mut v_a_389_: *mut lean_object = core::ptr::null_mut(); let mut v_a_390_: *mut lean_object = core::ptr::null_mut(); 
v_a_389_ = lean_ctor_get(v_x_382_, 0);
v_a_390_ = lean_ctor_get(v_x_382_, 1);
v_f_384_ = v_a_389_;
v_g_385_ = v_a_390_;
state = 1; continue;
}
3 => {
let mut v_a_391_: *mut lean_object = core::ptr::null_mut(); let mut v_a_392_: *mut lean_object = core::ptr::null_mut(); 
v_a_391_ = lean_ctor_get(v_x_382_, 0);
v_a_392_ = lean_ctor_get(v_x_382_, 1);
v_f_384_ = v_a_391_;
v_g_385_ = v_a_392_;
state = 1; continue;
}
4 => {
let mut v_a_393_: *mut lean_object = core::ptr::null_mut(); let mut v_a_394_: *mut lean_object = core::ptr::null_mut(); 
v_a_393_ = lean_ctor_get(v_x_382_, 0);
v_a_394_ = lean_ctor_get(v_x_382_, 1);
v_f_384_ = v_a_393_;
v_g_385_ = v_a_394_;
state = 1; continue;
}
5 => {
let mut v_a_395_: *mut lean_object = core::ptr::null_mut(); 
v_a_395_ = lean_ctor_get(v_x_382_, 0);
v_x_382_ = v_a_395_;
state = 0; continue;
}
_ => {
let mut v___x_397_: *mut lean_object = core::ptr::null_mut(); 
v___x_397_ = lean_unsigned_to_nat(1);
return v___x_397_;
}
}
}
1 => {
v___x_386_ = l_Expr_count(v_f_384_);
v___x_387_ = l_Expr_count(v_g_385_);
v___x_388_ = lean_nat_add(v___x_386_, v___x_387_);
lean_dec(v___x_387_);
lean_dec(v___x_386_);
return v___x_388_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_count___boxed(mut v_x_398_: *mut lean_object) -> *mut lean_object{
let mut v_res_399_: *mut lean_object = core::ptr::null_mut(); 
v_res_399_ = l_Expr_count(v_x_398_);
lean_dec_ref(v_x_398_);
return v_res_399_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_nestAux(mut v_s_400_: *mut lean_object, mut v_f_401_: *mut lean_object, mut v_x_402_: *mut lean_object, mut v_x_403_: *mut lean_object) -> *mut lean_object{
let mut v_zero_405_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_406_: u8 = 0; let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); let mut v_a_410_: *mut lean_object = core::ptr::null_mut(); let mut v_one_411_: *mut lean_object = core::ptr::null_mut(); let mut v_n_412_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_405_ = lean_unsigned_to_nat(0);
v_isZero_406_ = lean_nat_dec_eq(v_x_402_, v_zero_405_);
if v_isZero_406_ == 1 {
let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_402_);
lean_dec_ref(v_f_401_);
v___x_407_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_407_, 0, v_x_403_);
return v___x_407_;
} else {
let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); 
v___x_408_ = lean_nat_sub(v_s_400_, v_x_402_);
lean_inc_ref(v_f_401_);
v___x_409_ = lean_apply_3(v_f_401_, v___x_408_, v_x_403_, lean_box(0));
if lean_obj_tag(v___x_409_) == 0 {
let mut v_a_410_: *mut lean_object = core::ptr::null_mut(); let mut v_one_411_: *mut lean_object = core::ptr::null_mut(); let mut v_n_412_: *mut lean_object = core::ptr::null_mut(); 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v_one_411_ = lean_unsigned_to_nat(1);
v_n_412_ = lean_nat_sub(v_x_402_, v_one_411_);
lean_dec(v_x_402_);
v_x_402_ = v_n_412_;
v_x_403_ = v_a_410_;
state = 0; continue;
} else {
lean_dec(v_x_402_);
lean_dec_ref(v_f_401_);
return v___x_409_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_nestAux___boxed(mut v_s_414_: *mut lean_object, mut v_f_415_: *mut lean_object, mut v_x_416_: *mut lean_object, mut v_x_417_: *mut lean_object, mut v_a_418_: *mut lean_object) -> *mut lean_object{
let mut v_res_419_: *mut lean_object = core::ptr::null_mut(); 
v_res_419_ = l_Expr_nestAux(v_s_414_, v_f_415_, v_x_416_, v_x_417_);
lean_dec(v_s_414_);
return v_res_419_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_nest(mut v_f_420_: *mut lean_object, mut v_n_421_: *mut lean_object, mut v_e_422_: *mut lean_object) -> *mut lean_object{
let mut v___x_424_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_n_421_);
v___x_424_ = l_Expr_nestAux(v_n_421_, v_f_420_, v_n_421_, v_e_422_);
lean_dec(v_n_421_);
return v___x_424_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_nest___boxed(mut v_f_425_: *mut lean_object, mut v_n_426_: *mut lean_object, mut v_e_427_: *mut lean_object, mut v_a_428_: *mut lean_object) -> *mut lean_object{
let mut v_res_429_: *mut lean_object = core::ptr::null_mut(); 
v_res_429_ = l_Expr_nest(v_f_425_, v_n_426_, v_e_427_);
return v_res_429_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0(mut v_s_430_: *mut lean_object) -> *mut lean_object{
let mut v___x_432_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_433_: *mut lean_object = core::ptr::null_mut(); let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); 
v___x_432_ = lean_get_stdout();
v_putStr_433_ = lean_ctor_get(v___x_432_, 4);
lean_inc_ref(v_putStr_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = lean_apply_2(v_putStr_433_, v_s_430_, lean_box(0));
return v___x_434_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0___boxed(mut v_s_435_: *mut lean_object, mut v_a_436_: *mut lean_object) -> *mut lean_object{
let mut v_res_437_: *mut lean_object = core::ptr::null_mut(); 
v_res_437_ = l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0(v_s_435_);
return v_res_437_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00Expr_deriv_spec__0(mut v_s_438_: *mut lean_object) -> *mut lean_object{
let mut v___x_440_: u32 = 0; let mut v___x_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); 
v___x_440_ = 10;
v___x_441_ = lean_string_push(v_s_438_, v___x_440_);
v___x_442_ = l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0(v___x_441_);
return v___x_442_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00Expr_deriv_spec__0___boxed(mut v_s_443_: *mut lean_object, mut v_a_444_: *mut lean_object) -> *mut lean_object{
let mut v_res_445_: *mut lean_object = core::ptr::null_mut(); 
v_res_445_ = l_IO_println___at___00Expr_deriv_spec__0(v_s_443_);
return v_res_445_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_deriv(mut v_i_448_: *mut lean_object, mut v_f_449_: *mut lean_object) -> *mut lean_object{
let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v_d_452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_453_: *mut lean_object = core::ptr::null_mut(); let mut v___x_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); let mut v___x_458_: *mut lean_object = core::ptr::null_mut(); let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); let mut v___x_460_: *mut lean_object = core::ptr::null_mut(); let mut v___x_461_: *mut lean_object = core::ptr::null_mut(); let mut v___x_462_: *mut lean_object = core::ptr::null_mut(); let mut v___x_463_: *mut lean_object = core::ptr::null_mut(); let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_466_: u8 = 0; let mut v___x_468_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_469_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_470_: u8 = 0; let mut v_unused_471_: *mut lean_object = core::ptr::null_mut(); let mut v_a_472_: *mut lean_object = core::ptr::null_mut(); let mut v___x_474_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_475_: u8 = 0; let mut v___x_477_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_478_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_479_: u8 = 0; let mut v_a_480_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_483_: u8 = 0; let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_486_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_487_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_451_ = l_Expr_deriv___closed__0;
v_d_452_ = l_Expr_d(v___x_451_, v_f_449_);
v___x_453_ = lean_unsigned_to_nat(1);
v___x_454_ = lean_nat_add(v_i_448_, v___x_453_);
v___x_455_ = l_Nat_reprFast(v___x_454_);
v___x_456_ = l_Expr_deriv___closed__1;
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
v___x_458_ = l_Expr_count(v_d_452_);
v___x_459_ = l_Nat_reprFast(v___x_458_);
v___x_460_ = lean_string_append(v___x_457_, v___x_459_);
lean_dec_ref(v___x_459_);
v___x_461_ = l_IO_println___at___00Expr_deriv_spec__0(v___x_460_);
if lean_obj_tag(v___x_461_) == 0 {
let mut v___x_462_: *mut lean_object = core::ptr::null_mut(); let mut v___x_463_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_461_, 1);
v___x_462_ = l_Expr_Expr_toString(v_d_452_);
v___x_463_ = l_IO_println___at___00Expr_deriv_spec__0(v___x_462_);
if lean_obj_tag(v___x_463_) == 0 {
let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_466_: u8 = 0; let mut v_isSharedCheck_470_: u8 = 0; 
v_isSharedCheck_470_ = (!lean_is_exclusive(v___x_463_)) as u8;
if v_isSharedCheck_470_ == 0 {
let mut v_unused_471_: *mut lean_object = core::ptr::null_mut(); 
v_unused_471_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_471_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_470_;
state = 1; continue;
} else {
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
state = 1; continue;
}
} else {
let mut v_a_472_: *mut lean_object = core::ptr::null_mut(); let mut v___x_474_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_475_: u8 = 0; let mut v_isSharedCheck_479_: u8 = 0; 
lean_dec_ref(v_d_452_);
v_a_472_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_479_ = (!lean_is_exclusive(v___x_463_)) as u8;
if v_isSharedCheck_479_ == 0 {
v___x_474_ = v___x_463_;
v_isShared_475_ = v_isSharedCheck_479_;
state = 3; continue;
} else {
lean_inc(v_a_472_);
lean_dec(v___x_463_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
state = 3; continue;
}
}
} else {
let mut v_a_480_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_483_: u8 = 0; let mut v_isSharedCheck_487_: u8 = 0; 
lean_dec_ref(v_d_452_);
v_a_480_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_487_ = (!lean_is_exclusive(v___x_461_)) as u8;
if v_isSharedCheck_487_ == 0 {
v___x_482_ = v___x_461_;
v_isShared_483_ = v_isSharedCheck_487_;
state = 5; continue;
} else {
lean_inc(v_a_480_);
lean_dec(v___x_461_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
state = 5; continue;
}
}
}
1 => {
if v_isShared_466_ == 0 {
lean_ctor_set(v___x_465_, 0, v_d_452_);
v___x_468_ = v___x_465_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_469_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_d_452_);
v___x_468_ = v_reuseFailAlloc_469_;
state = 2; continue;
}
}
3 => {
if v_isShared_475_ == 0 {
v___x_477_ = v___x_474_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_478_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
state = 4; continue;
}
}
5 => {
if v_isShared_483_ == 0 {
v___x_485_ = v___x_482_;
state = 6; continue;
} else {
let mut v_reuseFailAlloc_486_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
state = 6; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_deriv___boxed(mut v_i_488_: *mut lean_object, mut v_f_489_: *mut lean_object, mut v_a_490_: *mut lean_object) -> *mut lean_object{
let mut v_res_491_: *mut lean_object = core::ptr::null_mut(); 
v_res_491_ = l_Expr_deriv(v_i_488_, v_f_489_);
lean_dec(v_i_488_);
return v_res_491_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_492_: *mut lean_object) -> *mut lean_object{
let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: u32 = 0; let mut v___x_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); 
v___x_494_ = l_Expr_Expr_toString(v_s_492_);
v___x_495_ = 10;
v___x_496_ = lean_string_push(v___x_494_, v___x_495_);
v___x_497_ = l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0(v___x_496_);
return v___x_497_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_498_: *mut lean_object, mut v_a_499_: *mut lean_object) -> *mut lean_object{
let mut v_res_500_: *mut lean_object = core::ptr::null_mut(); 
v_res_500_ = l_IO_println___at___00main_spec__0(v_s_498_);
lean_dec_ref(v_s_498_);
return v_res_500_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__1() -> *mut lean_object{
let mut v_x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); 
v_x_503_ = l_main___redArg___closed__0;
v___x_504_ = l_Expr_addAux(v_x_503_, v_x_503_);
return v___x_504_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__2() -> *mut lean_object{
let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v_x_506_: *mut lean_object = core::ptr::null_mut(); let mut v___x_507_: *mut lean_object = core::ptr::null_mut(); 
v___x_505_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__1), core::ptr::addr_of_mut!(l_main___redArg___closed__1_once), _init_l_main___redArg___closed__1);
v_x_506_ = l_main___redArg___closed__0;
v___x_507_ = l_Expr_mulAux(v_x_506_, v___x_505_);
return v___x_507_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__3() -> *mut lean_object{
let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); let mut v_x_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); 
v___x_508_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__2), core::ptr::addr_of_mut!(l_main___redArg___closed__2_once), _init_l_main___redArg___closed__2);
v_x_509_ = l_main___redArg___closed__0;
v___x_510_ = l_Expr_mulAux(v_x_509_, v___x_508_);
return v___x_510_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__4() -> *mut lean_object{
let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); let mut v_x_512_: *mut lean_object = core::ptr::null_mut(); let mut v_f_513_: *mut lean_object = core::ptr::null_mut(); 
v___x_511_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__3), core::ptr::addr_of_mut!(l_main___redArg___closed__3_once), _init_l_main___redArg___closed__3);
v_x_512_ = l_main___redArg___closed__0;
v_f_513_ = l_Expr_addAux(v_x_512_, v___x_511_);
return v_f_513_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___boxed__const__1() -> *mut lean_object{
let mut v___x_515_: u32 = 0; let mut v___x_516_: *mut lean_object = core::ptr::null_mut(); 
v___x_515_ = 0;
v___x_516_ = lean_box_uint32(v___x_515_);
return v___x_516_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v_f_518_: *mut lean_object = core::ptr::null_mut(); let mut v___x_519_: *mut lean_object = core::ptr::null_mut(); let mut v___x_520_: *mut lean_object = core::ptr::null_mut(); let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); let mut v___x_522_: *mut lean_object = core::ptr::null_mut(); let mut v___x_524_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_525_: u8 = 0; let mut v___x_526_: *mut lean_object = core::ptr::null_mut(); let mut v___x_528_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_529_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_530_: u8 = 0; let mut v_unused_531_: *mut lean_object = core::ptr::null_mut(); let mut v_a_532_: *mut lean_object = core::ptr::null_mut(); let mut v___x_534_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_535_: u8 = 0; let mut v___x_537_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_538_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_539_: u8 = 0; let mut v_a_540_: *mut lean_object = core::ptr::null_mut(); let mut v___x_542_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_543_: u8 = 0; let mut v___x_545_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_546_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_547_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_f_518_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__4), core::ptr::addr_of_mut!(l_main___redArg___closed__4_once), _init_l_main___redArg___closed__4);
v___x_519_ = l_IO_println___at___00main_spec__0(v_f_518_);
if lean_obj_tag(v___x_519_) == 0 {
let mut v___x_520_: *mut lean_object = core::ptr::null_mut(); let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); let mut v___x_522_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_519_, 1);
v___x_520_ = l_main___redArg___closed__5;
v___x_521_ = lean_unsigned_to_nat(3);
v___x_522_ = l_Expr_nestAux(v___x_521_, v___x_520_, v___x_521_, v_f_518_);
if lean_obj_tag(v___x_522_) == 0 {
let mut v___x_524_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_525_: u8 = 0; let mut v_isSharedCheck_530_: u8 = 0; 
v_isSharedCheck_530_ = (!lean_is_exclusive(v___x_522_)) as u8;
if v_isSharedCheck_530_ == 0 {
let mut v_unused_531_: *mut lean_object = core::ptr::null_mut(); 
v_unused_531_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_531_);
v___x_524_ = v___x_522_;
v_isShared_525_ = v_isSharedCheck_530_;
state = 1; continue;
} else {
lean_dec(v___x_522_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
state = 1; continue;
}
} else {
let mut v_a_532_: *mut lean_object = core::ptr::null_mut(); let mut v___x_534_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_535_: u8 = 0; let mut v_isSharedCheck_539_: u8 = 0; 
v_a_532_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_539_ = (!lean_is_exclusive(v___x_522_)) as u8;
if v_isSharedCheck_539_ == 0 {
v___x_534_ = v___x_522_;
v_isShared_535_ = v_isSharedCheck_539_;
state = 3; continue;
} else {
lean_inc(v_a_532_);
lean_dec(v___x_522_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
state = 3; continue;
}
}
} else {
let mut v_a_540_: *mut lean_object = core::ptr::null_mut(); let mut v___x_542_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_543_: u8 = 0; let mut v_isSharedCheck_547_: u8 = 0; 
v_a_540_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_547_ = (!lean_is_exclusive(v___x_519_)) as u8;
if v_isSharedCheck_547_ == 0 {
v___x_542_ = v___x_519_;
v_isShared_543_ = v_isSharedCheck_547_;
state = 5; continue;
} else {
lean_inc(v_a_540_);
lean_dec(v___x_519_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
state = 5; continue;
}
}
}
1 => {
v___x_526_ = l_main___redArg___boxed__const__1;
if v_isShared_525_ == 0 {
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_529_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
state = 2; continue;
}
}
3 => {
if v_isShared_535_ == 0 {
v___x_537_ = v___x_534_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_538_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
state = 4; continue;
}
}
5 => {
if v_isShared_543_ == 0 {
v___x_545_ = v___x_542_;
state = 6; continue;
} else {
let mut v_reuseFailAlloc_546_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
state = 6; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_548_: *mut lean_object) -> *mut lean_object{
let mut v_res_549_: *mut lean_object = core::ptr::null_mut(); 
v_res_549_ = l_main___redArg();
return v_res_549_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_550_: *mut lean_object) -> *mut lean_object{
let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_xs_550_);
v___x_552_ = l_main___redArg();
return v___x_552_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_553_: *mut lean_object, mut v_a_554_: *mut lean_object) -> *mut lean_object{
let mut v_res_555_: *mut lean_object = core::ptr::null_mut(); 
v_res_555_ = _lean_main(v_xs_553_);
return v_res_555_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_t4(builtin: u8) -> *mut lean_object {
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
  let res = initialize_t4(1 /* builtin */);
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
