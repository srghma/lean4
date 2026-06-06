// Lean compiler output
// Module: deriv
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
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_add(_: u32, _: u32) -> u32;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_int_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_int_neg(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_uint32_to_nat(_: u32) -> *mut lean_object;
}
static mut l_Expr_pown___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_pown___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_pown___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_pown___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_pown___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_pown___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_mul___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_mul___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_pow___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_pow___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_d___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_d___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_Expr_d___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Expr_d___closed__1: *mut lean_object = core::ptr::null_mut();
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
#[no_mangle] pub static l_Expr_deriv___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Expr_deriv___closed__0: *mut lean_object = core::ptr::addr_of!(l_Expr_deriv___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_deriv___closed__1_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [32, 99, 111, 117, 110, 116, 58, 32, 0]};
static mut l_Expr_deriv___closed__1: *mut lean_object = core::ptr::addr_of!(l_Expr_deriv___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l_Expr_deriv___closed__0_value) as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__2_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Expr_deriv___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_main___boxed__const__2: *mut lean_object = core::ptr::null_mut();
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
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_pown___closed__0() -> *mut lean_object{
let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); 
v___x_81_ = lean_unsigned_to_nat(0);
v___x_82_ = lean_nat_to_int(v___x_81_);
return v___x_82_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_pown___closed__1() -> *mut lean_object{
let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); 
v___x_83_ = lean_unsigned_to_nat(1);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_pown___closed__2() -> *mut lean_object{
let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); 
v___x_85_ = lean_unsigned_to_nat(2);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_pown(mut v_x_87_: *mut lean_object, mut v_x_88_: *mut lean_object) -> *mut lean_object{
let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: u8 = 0; 
v___x_89_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_90_ = lean_int_dec_eq(v_x_88_, v___x_89_);
if v___x_90_ == 0 {
let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: u8 = 0; 
v___x_91_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_92_ = lean_int_dec_eq(v_x_88_, v___x_91_);
if v___x_92_ == 0 {
let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v_b_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: u8 = 0; 
v___x_93_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__2), core::ptr::addr_of_mut!(l_Expr_pown___closed__2_once), _init_l_Expr_pown___closed__2);
v___x_94_ = lean_int_ediv(v_x_88_, v___x_93_);
v_b_95_ = l_Expr_pown(v_x_87_, v___x_94_);
lean_dec(v___x_94_);
v___x_96_ = lean_int_mul(v_b_95_, v_b_95_);
lean_dec(v_b_95_);
v___x_97_ = lean_int_emod(v_x_88_, v___x_93_);
v___x_98_ = lean_int_dec_eq(v___x_97_, v___x_89_);
lean_dec(v___x_97_);
if v___x_98_ == 0 {
let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); 
v___x_99_ = lean_int_mul(v___x_96_, v_x_87_);
lean_dec(v___x_96_);
return v___x_99_;
} else {
let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); 
v___x_100_ = lean_int_mul(v___x_96_, v___x_91_);
lean_dec(v___x_96_);
return v___x_100_;
}
} else {
lean_inc(v_x_87_);
return v_x_87_;
}
} else {
let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); 
v___x_101_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
return v___x_101_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_pown___boxed(mut v_x_102_: *mut lean_object, mut v_x_103_: *mut lean_object) -> *mut lean_object{
let mut v_res_104_: *mut lean_object = core::ptr::null_mut(); 
v_res_104_ = l_Expr_pown(v_x_102_, v_x_103_);
lean_dec(v_x_103_);
lean_dec(v_x_102_);
return v_res_104_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_add(mut v_x_105_: *mut lean_object, mut v_x_106_: *mut lean_object) -> *mut lean_object{
let mut v_f_108_: *mut lean_object = core::ptr::null_mut(); let mut v_n_109_: *mut lean_object = core::ptr::null_mut(); let mut v_g_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v_f_115_: *mut lean_object = core::ptr::null_mut(); let mut v_n_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); let mut v_a_119_: *mut lean_object = core::ptr::null_mut(); let mut v_a_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_123_: u8 = 0; let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_127_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_128_: u8 = 0; let mut v_a_129_: *mut lean_object = core::ptr::null_mut(); let mut v_a_130_: *mut lean_object = core::ptr::null_mut(); let mut v_a_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: u8 = 0; let mut v_a_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_137_: u8 = 0; let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_142_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_143_: u8 = 0; let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v_a_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: u8 = 0; let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v_a_149_: *mut lean_object = core::ptr::null_mut(); let mut v_a_150_: *mut lean_object = core::ptr::null_mut(); let mut v_h_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v_a_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: u8 = 0; let mut v_a_158_: *mut lean_object = core::ptr::null_mut(); let mut v_a_159_: *mut lean_object = core::ptr::null_mut(); let mut v_a_160_: *mut lean_object = core::ptr::null_mut(); let mut v_a_161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: u8 = 0; let mut v_a_164_: *mut lean_object = core::ptr::null_mut(); let mut v_a_165_: *mut lean_object = core::ptr::null_mut(); let mut v_a_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_105_)
{
0 => {
match lean_obj_tag(v_x_106_)
{
0 => {
let mut v_a_119_: *mut lean_object = core::ptr::null_mut(); let mut v_a_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_123_: u8 = 0; let mut v_isSharedCheck_128_: u8 = 0; 
v_a_119_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v_x_105_, 1);
v_a_120_ = lean_ctor_get(v_x_106_, 0);
v_isSharedCheck_128_ = (!lean_is_exclusive(v_x_106_)) as u8;
if v_isSharedCheck_128_ == 0 {
v___x_122_ = v_x_106_;
v_isShared_123_ = v_isSharedCheck_128_;
state = 3; continue;
} else {
lean_inc(v_a_120_);
lean_dec(v_x_106_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_128_;
state = 3; continue;
}
}
2 => {
let mut v_a_129_: *mut lean_object = core::ptr::null_mut(); let mut v_a_130_: *mut lean_object = core::ptr::null_mut(); let mut v_a_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: u8 = 0; 
v_a_129_ = lean_ctor_get(v_x_105_, 0);
v_a_130_ = lean_ctor_get(v_x_106_, 0);
lean_inc_ref(v_a_130_);
v_a_131_ = lean_ctor_get(v_x_106_, 1);
v___x_132_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_133_ = lean_int_dec_eq(v_a_129_, v___x_132_);
if v___x_133_ == 0 {
if lean_obj_tag(v_a_130_) == 0 {
let mut v_a_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_137_: u8 = 0; let mut v_isSharedCheck_143_: u8 = 0; 
lean_inc_ref(v_a_131_);
lean_inc(v_a_129_);
lean_dec_ref_known(v_x_106_, 2);
lean_dec_ref_known(v_x_105_, 1);
v_a_134_ = lean_ctor_get(v_a_130_, 0);
v_isSharedCheck_143_ = (!lean_is_exclusive(v_a_130_)) as u8;
if v_isSharedCheck_143_ == 0 {
v___x_136_ = v_a_130_;
v_isShared_137_ = v_isSharedCheck_143_;
state = 5; continue;
} else {
lean_inc(v_a_134_);
lean_dec(v_a_130_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_143_;
state = 5; continue;
}
} else {
let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_a_130_);
v___x_144_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_144_, 0, v_x_105_);
lean_ctor_set(v___x_144_, 1, v_x_106_);
return v___x_144_;
}
} else {
lean_dec_ref(v_a_130_);
lean_dec_ref_known(v_x_105_, 1);
return v_x_106_;
}
}
_ => {
let mut v_a_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: u8 = 0; 
v_a_145_ = lean_ctor_get(v_x_105_, 0);
v___x_146_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_147_ = lean_int_dec_eq(v_a_145_, v___x_146_);
if v___x_147_ == 0 {
let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); 
v___x_148_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_148_, 0, v_x_105_);
lean_ctor_set(v___x_148_, 1, v_x_106_);
return v___x_148_;
} else {
lean_dec_ref_known(v_x_105_, 1);
return v_x_106_;
}
}
}
}
2 => {
let mut v_a_149_: *mut lean_object = core::ptr::null_mut(); let mut v_a_150_: *mut lean_object = core::ptr::null_mut(); let mut v_h_152_: *mut lean_object = core::ptr::null_mut(); 
v_a_149_ = lean_ctor_get(v_x_105_, 0);
v_a_150_ = lean_ctor_get(v_x_105_, 1);
match lean_obj_tag(v_x_106_)
{
0 => {
let mut v_a_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: u8 = 0; 
v_a_155_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v_x_106_, 1);
v___x_156_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_157_ = lean_int_dec_eq(v_a_155_, v___x_156_);
if v___x_157_ == 0 {
v_f_115_ = v_x_105_;
v_n_116_ = v_a_155_;
state = 2; continue;
} else {
lean_dec(v_a_155_);
return v_x_105_;
}
}
2 => {
let mut v_a_158_: *mut lean_object = core::ptr::null_mut(); 
v_a_158_ = lean_ctor_get(v_x_106_, 0);
if lean_obj_tag(v_a_158_) == 0 {
let mut v_a_159_: *mut lean_object = core::ptr::null_mut(); let mut v_a_160_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_158_);
v_a_159_ = lean_ctor_get(v_x_106_, 1);
lean_inc_ref(v_a_159_);
lean_dec_ref_known(v_x_106_, 2);
v_a_160_ = lean_ctor_get(v_a_158_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v_a_158_, 1);
v_f_108_ = v_x_105_;
v_n_109_ = v_a_160_;
v_g_110_ = v_a_159_;
state = 1; continue;
} else {
lean_inc_ref(v_a_150_);
lean_inc_ref(v_a_149_);
lean_dec_ref_known(v_x_105_, 2);
v_h_152_ = v_x_106_;
state = 7; continue;
}
}
_ => {
lean_inc_ref(v_a_150_);
lean_inc_ref(v_a_149_);
lean_dec_ref_known(v_x_105_, 2);
v_h_152_ = v_x_106_;
state = 7; continue;
}
}
}
_ => {
match lean_obj_tag(v_x_106_)
{
0 => {
let mut v_a_161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: u8 = 0; 
v_a_161_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v_x_106_, 1);
v___x_162_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_163_ = lean_int_dec_eq(v_a_161_, v___x_162_);
if v___x_163_ == 0 {
v_f_115_ = v_x_105_;
v_n_116_ = v_a_161_;
state = 2; continue;
} else {
lean_dec(v_a_161_);
return v_x_105_;
}
}
2 => {
let mut v_a_164_: *mut lean_object = core::ptr::null_mut(); 
v_a_164_ = lean_ctor_get(v_x_106_, 0);
if lean_obj_tag(v_a_164_) == 0 {
let mut v_a_165_: *mut lean_object = core::ptr::null_mut(); let mut v_a_166_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_164_);
v_a_165_ = lean_ctor_get(v_x_106_, 1);
lean_inc_ref(v_a_165_);
lean_dec_ref_known(v_x_106_, 2);
v_a_166_ = lean_ctor_get(v_a_164_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v_a_164_, 1);
v_f_108_ = v_x_105_;
v_n_109_ = v_a_166_;
v_g_110_ = v_a_165_;
state = 1; continue;
} else {
let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); 
v___x_167_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_167_, 0, v_x_105_);
lean_ctor_set(v___x_167_, 1, v_x_106_);
return v___x_167_;
}
}
_ => {
let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); 
v___x_168_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_168_, 0, v_x_105_);
lean_ctor_set(v___x_168_, 1, v_x_106_);
return v___x_168_;
}
}
}
}
}
1 => {
v___x_111_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_111_, 0, v_n_109_);
v___x_112_ = l_Expr_add(v_f_108_, v_g_110_);
v_x_105_ = v___x_111_;
v_x_106_ = v___x_112_;
state = 0; continue;
}
2 => {
v___x_117_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_117_, 0, v_n_116_);
v_x_105_ = v___x_117_;
v_x_106_ = v_f_115_;
state = 0; continue;
}
3 => {
v___x_124_ = lean_int_add(v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec(v_a_119_);
if v_isShared_123_ == 0 {
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_126_ = v___x_122_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_127_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
state = 4; continue;
}
}
5 => {
v___x_138_ = lean_int_add(v_a_129_, v_a_134_);
lean_dec(v_a_134_);
lean_dec(v_a_129_);
if v_isShared_137_ == 0 {
lean_ctor_set(v___x_136_, 0, v___x_138_);
v___x_140_ = v___x_136_;
state = 6; continue;
} else {
let mut v_reuseFailAlloc_142_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_142_;
state = 6; continue;
}
}
7 => {
v___x_153_ = l_Expr_add(v_a_150_, v_h_152_);
v_x_105_ = v_a_149_;
v_x_106_ = v___x_153_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_mul___closed__0() -> *mut lean_object{
let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); 
v___x_169_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_170_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_mul(mut v_x_171_: *mut lean_object, mut v_x_172_: *mut lean_object) -> *mut lean_object{
let mut v_f_174_: *mut lean_object = core::ptr::null_mut(); let mut v_n_175_: *mut lean_object = core::ptr::null_mut(); let mut v_g_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v_f_181_: *mut lean_object = core::ptr::null_mut(); let mut v_n_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_186_: *mut lean_object = core::ptr::null_mut(); let mut v_a_187_: *mut lean_object = core::ptr::null_mut(); let mut v_a_188_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_191_: u8 = 0; let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_195_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_196_: u8 = 0; let mut v_a_197_: *mut lean_object = core::ptr::null_mut(); let mut v_a_198_: *mut lean_object = core::ptr::null_mut(); let mut v_a_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: u8 = 0; let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: u8 = 0; let mut v_a_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_207_: u8 = 0; let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_212_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_213_: u8 = 0; let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v_a_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: u8 = 0; let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: u8 = 0; let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v_a_221_: *mut lean_object = core::ptr::null_mut(); let mut v_a_222_: *mut lean_object = core::ptr::null_mut(); let mut v_h_224_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v_a_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: u8 = 0; let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: u8 = 0; let mut v_a_232_: *mut lean_object = core::ptr::null_mut(); let mut v_a_233_: *mut lean_object = core::ptr::null_mut(); let mut v_a_234_: *mut lean_object = core::ptr::null_mut(); let mut v_a_235_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); let mut v___x_237_: u8 = 0; let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v___x_239_: u8 = 0; let mut v_a_240_: *mut lean_object = core::ptr::null_mut(); let mut v_a_241_: *mut lean_object = core::ptr::null_mut(); let mut v_a_242_: *mut lean_object = core::ptr::null_mut(); let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_171_)
{
0 => {
match lean_obj_tag(v_x_172_)
{
0 => {
let mut v_a_187_: *mut lean_object = core::ptr::null_mut(); let mut v_a_188_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_191_: u8 = 0; let mut v_isSharedCheck_196_: u8 = 0; 
v_a_187_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v_x_171_, 1);
v_a_188_ = lean_ctor_get(v_x_172_, 0);
v_isSharedCheck_196_ = (!lean_is_exclusive(v_x_172_)) as u8;
if v_isSharedCheck_196_ == 0 {
v___x_190_ = v_x_172_;
v_isShared_191_ = v_isSharedCheck_196_;
state = 4; continue;
} else {
lean_inc(v_a_188_);
lean_dec(v_x_172_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
state = 4; continue;
}
}
3 => {
let mut v_a_197_: *mut lean_object = core::ptr::null_mut(); let mut v_a_198_: *mut lean_object = core::ptr::null_mut(); let mut v_a_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: u8 = 0; 
v_a_197_ = lean_ctor_get(v_x_171_, 0);
v_a_198_ = lean_ctor_get(v_x_172_, 0);
lean_inc_ref(v_a_198_);
v_a_199_ = lean_ctor_get(v_x_172_, 1);
v___x_200_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_201_ = lean_int_dec_eq(v_a_197_, v___x_200_);
if v___x_201_ == 0 {
let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: u8 = 0; 
v___x_202_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_203_ = lean_int_dec_eq(v_a_197_, v___x_202_);
if v___x_203_ == 0 {
if lean_obj_tag(v_a_198_) == 0 {
let mut v_a_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_207_: u8 = 0; let mut v_isSharedCheck_213_: u8 = 0; 
lean_inc_ref(v_a_199_);
lean_inc(v_a_197_);
lean_dec_ref_known(v_x_172_, 2);
lean_dec_ref_known(v_x_171_, 1);
v_a_204_ = lean_ctor_get(v_a_198_, 0);
v_isSharedCheck_213_ = (!lean_is_exclusive(v_a_198_)) as u8;
if v_isSharedCheck_213_ == 0 {
v___x_206_ = v_a_198_;
v_isShared_207_ = v_isSharedCheck_213_;
state = 6; continue;
} else {
lean_inc(v_a_204_);
lean_dec(v_a_198_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_213_;
state = 6; continue;
}
} else {
let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_a_198_);
v___x_214_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_214_, 0, v_x_171_);
lean_ctor_set(v___x_214_, 1, v_x_172_);
return v___x_214_;
}
} else {
lean_dec_ref(v_a_198_);
lean_dec_ref_known(v_x_171_, 1);
return v_x_172_;
}
} else {
lean_dec_ref(v_a_198_);
lean_dec_ref_known(v_x_172_, 2);
lean_dec_ref_known(v_x_171_, 1);
state = 3; continue;
}
}
_ => {
let mut v_a_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: u8 = 0; 
v_a_215_ = lean_ctor_get(v_x_171_, 0);
v___x_216_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_217_ = lean_int_dec_eq(v_a_215_, v___x_216_);
if v___x_217_ == 0 {
let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: u8 = 0; 
v___x_218_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_219_ = lean_int_dec_eq(v_a_215_, v___x_218_);
if v___x_219_ == 0 {
let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); 
v___x_220_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_220_, 0, v_x_171_);
lean_ctor_set(v___x_220_, 1, v_x_172_);
return v___x_220_;
} else {
lean_dec_ref_known(v_x_171_, 1);
return v_x_172_;
}
} else {
lean_dec_ref_known(v_x_171_, 1);
lean_dec_ref(v_x_172_);
state = 3; continue;
}
}
}
}
3 => {
let mut v_a_221_: *mut lean_object = core::ptr::null_mut(); let mut v_a_222_: *mut lean_object = core::ptr::null_mut(); let mut v_h_224_: *mut lean_object = core::ptr::null_mut(); 
v_a_221_ = lean_ctor_get(v_x_171_, 0);
v_a_222_ = lean_ctor_get(v_x_171_, 1);
match lean_obj_tag(v_x_172_)
{
0 => {
let mut v_a_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: u8 = 0; 
v_a_227_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v_x_172_, 1);
v___x_228_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_229_ = lean_int_dec_eq(v_a_227_, v___x_228_);
if v___x_229_ == 0 {
let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: u8 = 0; 
v___x_230_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_231_ = lean_int_dec_eq(v_a_227_, v___x_230_);
if v___x_231_ == 0 {
v_f_181_ = v_x_171_;
v_n_182_ = v_a_227_;
state = 2; continue;
} else {
lean_dec(v_a_227_);
return v_x_171_;
}
} else {
lean_dec(v_a_227_);
lean_dec_ref_known(v_x_171_, 2);
state = 3; continue;
}
}
3 => {
let mut v_a_232_: *mut lean_object = core::ptr::null_mut(); 
v_a_232_ = lean_ctor_get(v_x_172_, 0);
if lean_obj_tag(v_a_232_) == 0 {
let mut v_a_233_: *mut lean_object = core::ptr::null_mut(); let mut v_a_234_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_232_);
v_a_233_ = lean_ctor_get(v_x_172_, 1);
lean_inc_ref(v_a_233_);
lean_dec_ref_known(v_x_172_, 2);
v_a_234_ = lean_ctor_get(v_a_232_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v_a_232_, 1);
v_f_174_ = v_x_171_;
v_n_175_ = v_a_234_;
v_g_176_ = v_a_233_;
state = 1; continue;
} else {
lean_inc_ref(v_a_222_);
lean_inc_ref(v_a_221_);
lean_dec_ref_known(v_x_171_, 2);
v_h_224_ = v_x_172_;
state = 8; continue;
}
}
_ => {
lean_inc_ref(v_a_222_);
lean_inc_ref(v_a_221_);
lean_dec_ref_known(v_x_171_, 2);
v_h_224_ = v_x_172_;
state = 8; continue;
}
}
}
_ => {
match lean_obj_tag(v_x_172_)
{
0 => {
let mut v_a_235_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); let mut v___x_237_: u8 = 0; 
v_a_235_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v_x_172_, 1);
v___x_236_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_237_ = lean_int_dec_eq(v_a_235_, v___x_236_);
if v___x_237_ == 0 {
let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v___x_239_: u8 = 0; 
v___x_238_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_239_ = lean_int_dec_eq(v_a_235_, v___x_238_);
if v___x_239_ == 0 {
v_f_181_ = v_x_171_;
v_n_182_ = v_a_235_;
state = 2; continue;
} else {
lean_dec(v_a_235_);
return v_x_171_;
}
} else {
lean_dec(v_a_235_);
lean_dec_ref(v_x_171_);
state = 3; continue;
}
}
3 => {
let mut v_a_240_: *mut lean_object = core::ptr::null_mut(); 
v_a_240_ = lean_ctor_get(v_x_172_, 0);
if lean_obj_tag(v_a_240_) == 0 {
let mut v_a_241_: *mut lean_object = core::ptr::null_mut(); let mut v_a_242_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_240_);
v_a_241_ = lean_ctor_get(v_x_172_, 1);
lean_inc_ref(v_a_241_);
lean_dec_ref_known(v_x_172_, 2);
v_a_242_ = lean_ctor_get(v_a_240_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v_a_240_, 1);
v_f_174_ = v_x_171_;
v_n_175_ = v_a_242_;
v_g_176_ = v_a_241_;
state = 1; continue;
} else {
let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); 
v___x_243_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_243_, 0, v_x_171_);
lean_ctor_set(v___x_243_, 1, v_x_172_);
return v___x_243_;
}
}
_ => {
let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); 
v___x_244_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_244_, 0, v_x_171_);
lean_ctor_set(v___x_244_, 1, v_x_172_);
return v___x_244_;
}
}
}
}
}
1 => {
v___x_177_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_177_, 0, v_n_175_);
v___x_178_ = l_Expr_mul(v_f_174_, v_g_176_);
v_x_171_ = v___x_177_;
v_x_172_ = v___x_178_;
state = 0; continue;
}
2 => {
v___x_183_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_183_, 0, v_n_182_);
v_x_171_ = v___x_183_;
v_x_172_ = v_f_181_;
state = 0; continue;
}
3 => {
v___x_186_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mul___closed__0), core::ptr::addr_of_mut!(l_Expr_mul___closed__0_once), _init_l_Expr_mul___closed__0);
return v___x_186_;
}
4 => {
v___x_192_ = lean_int_mul(v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec(v_a_187_);
if v_isShared_191_ == 0 {
lean_ctor_set(v___x_190_, 0, v___x_192_);
v___x_194_ = v___x_190_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_195_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
state = 5; continue;
}
}
6 => {
v___x_208_ = lean_int_mul(v_a_197_, v_a_204_);
lean_dec(v_a_204_);
lean_dec(v_a_197_);
if v_isShared_207_ == 0 {
lean_ctor_set(v___x_206_, 0, v___x_208_);
v___x_210_ = v___x_206_;
state = 7; continue;
} else {
let mut v_reuseFailAlloc_212_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_212_;
state = 7; continue;
}
}
8 => {
v___x_225_ = l_Expr_mul(v_a_222_, v_h_224_);
v_x_171_ = v_a_221_;
v_x_172_ = v___x_225_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_pow___closed__0() -> *mut lean_object{
let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); 
v___x_245_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_246_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_pow(mut v_x_247_: *mut lean_object, mut v_x_248_: *mut lean_object) -> *mut lean_object{
let mut v_a_249_: *mut lean_object = core::ptr::null_mut(); let mut v_a_250_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_253_: u8 = 0; let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_257_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_258_: u8 = 0; let mut v_a_259_: *mut lean_object = core::ptr::null_mut(); let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_261_: u8 = 0; let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v_a_264_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: u8 = 0; let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: u8 = 0; let mut v___x_269_: *mut lean_object = core::ptr::null_mut(); let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_247_) == 0 {
if lean_obj_tag(v_x_248_) == 0 {
let mut v_a_249_: *mut lean_object = core::ptr::null_mut(); let mut v_a_250_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_253_: u8 = 0; let mut v_isSharedCheck_258_: u8 = 0; 
v_a_249_ = lean_ctor_get(v_x_247_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v_x_247_, 1);
v_a_250_ = lean_ctor_get(v_x_248_, 0);
v_isSharedCheck_258_ = (!lean_is_exclusive(v_x_248_)) as u8;
if v_isSharedCheck_258_ == 0 {
v___x_252_ = v_x_248_;
v_isShared_253_ = v_isSharedCheck_258_;
state = 1; continue;
} else {
lean_inc(v_a_250_);
lean_dec(v_x_248_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_258_;
state = 1; continue;
}
} else {
let mut v_a_259_: *mut lean_object = core::ptr::null_mut(); let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_261_: u8 = 0; 
v_a_259_ = lean_ctor_get(v_x_247_, 0);
v___x_260_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_261_ = lean_int_dec_eq(v_a_259_, v___x_260_);
if v___x_261_ == 0 {
let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); 
v___x_262_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_262_, 0, v_x_247_);
lean_ctor_set(v___x_262_, 1, v_x_248_);
return v___x_262_;
} else {
let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_247_, 1);
lean_dec_ref(v_x_248_);
v___x_263_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mul___closed__0), core::ptr::addr_of_mut!(l_Expr_mul___closed__0_once), _init_l_Expr_mul___closed__0);
return v___x_263_;
}
}
} else {
if lean_obj_tag(v_x_248_) == 0 {
let mut v_a_264_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: u8 = 0; 
v_a_264_ = lean_ctor_get(v_x_248_, 0);
v___x_265_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__0), core::ptr::addr_of_mut!(l_Expr_pown___closed__0_once), _init_l_Expr_pown___closed__0);
v___x_266_ = lean_int_dec_eq(v_a_264_, v___x_265_);
if v___x_266_ == 0 {
let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: u8 = 0; 
v___x_267_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_268_ = lean_int_dec_eq(v_a_264_, v___x_267_);
if v___x_268_ == 0 {
let mut v___x_269_: *mut lean_object = core::ptr::null_mut(); 
v___x_269_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_269_, 0, v_x_247_);
lean_ctor_set(v___x_269_, 1, v_x_248_);
return v___x_269_;
} else {
lean_dec_ref_known(v_x_248_, 1);
return v_x_247_;
}
} else {
let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_248_, 1);
lean_dec_ref(v_x_247_);
v___x_270_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pow___closed__0), core::ptr::addr_of_mut!(l_Expr_pow___closed__0_once), _init_l_Expr_pow___closed__0);
return v___x_270_;
}
} else {
let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); 
v___x_271_ = lean_alloc_ctor(4, 2, (0) as u32);
lean_ctor_set(v___x_271_, 0, v_x_247_);
lean_ctor_set(v___x_271_, 1, v_x_248_);
return v___x_271_;
}
}
}
1 => {
v___x_254_ = l_Expr_pown(v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec(v_a_249_);
if v_isShared_253_ == 0 {
lean_ctor_set(v___x_252_, 0, v___x_254_);
v___x_256_ = v___x_252_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_257_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ln(mut v_x_272_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_272_) == 0 {
let mut v_a_273_: *mut lean_object = core::ptr::null_mut(); let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); let mut v___x_275_: u8 = 0; 
v_a_273_ = lean_ctor_get(v_x_272_, 0);
v___x_274_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_275_ = lean_int_dec_eq(v_a_273_, v___x_274_);
if v___x_275_ == 0 {
let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); 
v___x_276_ = lean_alloc_ctor(5, 1, (0) as u32);
lean_ctor_set(v___x_276_, 0, v_x_272_);
return v___x_276_;
} else {
let mut v___x_277_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_272_, 1);
v___x_277_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mul___closed__0), core::ptr::addr_of_mut!(l_Expr_mul___closed__0_once), _init_l_Expr_mul___closed__0);
return v___x_277_;
}
} else {
let mut v___x_278_: *mut lean_object = core::ptr::null_mut(); 
v___x_278_ = lean_alloc_ctor(5, 1, (0) as u32);
lean_ctor_set(v___x_278_, 0, v_x_272_);
return v___x_278_;
}
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_d___closed__0() -> *mut lean_object{
let mut v___x_279_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: *mut lean_object = core::ptr::null_mut(); 
v___x_279_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pown___closed__1), core::ptr::addr_of_mut!(l_Expr_pown___closed__1_once), _init_l_Expr_pown___closed__1);
v___x_280_ = lean_int_neg(v___x_279_);
return v___x_280_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Expr_d___closed__1() -> *mut lean_object{
let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); 
v___x_281_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_d___closed__0), core::ptr::addr_of_mut!(l_Expr_d___closed__0_once), _init_l_Expr_d___closed__0);
v___x_282_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_d(mut v_x_283_: *mut lean_object, mut v_x_284_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_284_)
{
0 => {
let mut v___x_285_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_284_, 1);
v___x_285_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mul___closed__0), core::ptr::addr_of_mut!(l_Expr_mul___closed__0_once), _init_l_Expr_mul___closed__0);
return v___x_285_;
}
1 => {
let mut v_a_286_: *mut lean_object = core::ptr::null_mut(); let mut v___x_287_: u8 = 0; 
v_a_286_ = lean_ctor_get(v_x_284_, 0);
lean_inc_ref(v_a_286_);
lean_dec_ref_known(v_x_284_, 1);
v___x_287_ = lean_string_dec_eq(v_x_283_, v_a_286_);
lean_dec_ref(v_a_286_);
if v___x_287_ == 0 {
let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); 
v___x_288_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_mul___closed__0), core::ptr::addr_of_mut!(l_Expr_mul___closed__0_once), _init_l_Expr_mul___closed__0);
return v___x_288_;
} else {
let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); 
v___x_289_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_pow___closed__0), core::ptr::addr_of_mut!(l_Expr_pow___closed__0_once), _init_l_Expr_pow___closed__0);
return v___x_289_;
}
}
2 => {
let mut v_a_290_: *mut lean_object = core::ptr::null_mut(); let mut v_a_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); 
v_a_290_ = lean_ctor_get(v_x_284_, 0);
lean_inc_ref(v_a_290_);
v_a_291_ = lean_ctor_get(v_x_284_, 1);
lean_inc_ref(v_a_291_);
lean_dec_ref_known(v_x_284_, 2);
v___x_292_ = l_Expr_d(v_x_283_, v_a_290_);
v___x_293_ = l_Expr_d(v_x_283_, v_a_291_);
v___x_294_ = l_Expr_add(v___x_292_, v___x_293_);
return v___x_294_;
}
3 => {
let mut v_a_295_: *mut lean_object = core::ptr::null_mut(); let mut v_a_296_: *mut lean_object = core::ptr::null_mut(); let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); 
v_a_295_ = lean_ctor_get(v_x_284_, 0);
lean_inc_ref_n(v_a_295_, 2);
v_a_296_ = lean_ctor_get(v_x_284_, 1);
lean_inc_ref_n(v_a_296_, 2);
lean_dec_ref_known(v_x_284_, 2);
v___x_297_ = l_Expr_d(v_x_283_, v_a_296_);
v___x_298_ = l_Expr_mul(v_a_295_, v___x_297_);
v___x_299_ = l_Expr_d(v_x_283_, v_a_295_);
v___x_300_ = l_Expr_mul(v_a_296_, v___x_299_);
v___x_301_ = l_Expr_add(v___x_298_, v___x_300_);
return v___x_301_;
}
4 => {
let mut v_a_302_: *mut lean_object = core::ptr::null_mut(); let mut v_a_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_306_: *mut lean_object = core::ptr::null_mut(); let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); let mut v___x_308_: *mut lean_object = core::ptr::null_mut(); let mut v___x_309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_312_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); let mut v___x_314_: *mut lean_object = core::ptr::null_mut(); 
v_a_302_ = lean_ctor_get(v_x_284_, 0);
lean_inc_ref_n(v_a_302_, 4);
v_a_303_ = lean_ctor_get(v_x_284_, 1);
lean_inc_ref_n(v_a_303_, 3);
lean_dec_ref_known(v_x_284_, 2);
v___x_304_ = l_Expr_pow(v_a_302_, v_a_303_);
v___x_305_ = l_Expr_d(v_x_283_, v_a_302_);
v___x_306_ = l_Expr_mul(v_a_303_, v___x_305_);
v___x_307_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_d___closed__1), core::ptr::addr_of_mut!(l_Expr_d___closed__1_once), _init_l_Expr_d___closed__1);
v___x_308_ = l_Expr_pow(v_a_302_, v___x_307_);
v___x_309_ = l_Expr_mul(v___x_306_, v___x_308_);
v___x_310_ = l_Expr_ln(v_a_302_);
v___x_311_ = l_Expr_d(v_x_283_, v_a_303_);
v___x_312_ = l_Expr_mul(v___x_310_, v___x_311_);
v___x_313_ = l_Expr_add(v___x_309_, v___x_312_);
v___x_314_ = l_Expr_mul(v___x_304_, v___x_313_);
return v___x_314_;
}
_ => {
let mut v_a_315_: *mut lean_object = core::ptr::null_mut(); let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); let mut v___x_318_: *mut lean_object = core::ptr::null_mut(); let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); 
v_a_315_ = lean_ctor_get(v_x_284_, 0);
lean_inc_ref_n(v_a_315_, 2);
lean_dec_ref_known(v_x_284_, 1);
v___x_316_ = l_Expr_d(v_x_283_, v_a_315_);
v___x_317_ = lean_obj_once(core::ptr::addr_of_mut!(l_Expr_d___closed__1), core::ptr::addr_of_mut!(l_Expr_d___closed__1_once), _init_l_Expr_d___closed__1);
v___x_318_ = l_Expr_pow(v_a_315_, v___x_317_);
v___x_319_ = l_Expr_mul(v___x_316_, v___x_318_);
return v___x_319_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_d___boxed(mut v_x_320_: *mut lean_object, mut v_x_321_: *mut lean_object) -> *mut lean_object{
let mut v_res_322_: *mut lean_object = core::ptr::null_mut(); 
v_res_322_ = l_Expr_d(v_x_320_, v_x_321_);
lean_dec_ref(v_x_320_);
return v_res_322_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_count(mut v_x_323_: *mut lean_object) -> u32{
let mut v_f_325_: *mut lean_object = core::ptr::null_mut(); let mut v_g_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: u32 = 0; let mut v___x_328_: u32 = 0; let mut v___x_329_: u32 = 0; let mut v_a_330_: *mut lean_object = core::ptr::null_mut(); let mut v_a_331_: *mut lean_object = core::ptr::null_mut(); let mut v_a_332_: *mut lean_object = core::ptr::null_mut(); let mut v_a_333_: *mut lean_object = core::ptr::null_mut(); let mut v_a_334_: *mut lean_object = core::ptr::null_mut(); let mut v_a_335_: *mut lean_object = core::ptr::null_mut(); let mut v_a_336_: *mut lean_object = core::ptr::null_mut(); let mut v___x_338_: u32 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_323_)
{
2 => {
let mut v_a_330_: *mut lean_object = core::ptr::null_mut(); let mut v_a_331_: *mut lean_object = core::ptr::null_mut(); 
v_a_330_ = lean_ctor_get(v_x_323_, 0);
v_a_331_ = lean_ctor_get(v_x_323_, 1);
v_f_325_ = v_a_330_;
v_g_326_ = v_a_331_;
state = 1; continue;
}
3 => {
let mut v_a_332_: *mut lean_object = core::ptr::null_mut(); let mut v_a_333_: *mut lean_object = core::ptr::null_mut(); 
v_a_332_ = lean_ctor_get(v_x_323_, 0);
v_a_333_ = lean_ctor_get(v_x_323_, 1);
v_f_325_ = v_a_332_;
v_g_326_ = v_a_333_;
state = 1; continue;
}
4 => {
let mut v_a_334_: *mut lean_object = core::ptr::null_mut(); let mut v_a_335_: *mut lean_object = core::ptr::null_mut(); 
v_a_334_ = lean_ctor_get(v_x_323_, 0);
v_a_335_ = lean_ctor_get(v_x_323_, 1);
v_f_325_ = v_a_334_;
v_g_326_ = v_a_335_;
state = 1; continue;
}
5 => {
let mut v_a_336_: *mut lean_object = core::ptr::null_mut(); 
v_a_336_ = lean_ctor_get(v_x_323_, 0);
v_x_323_ = v_a_336_;
state = 0; continue;
}
_ => {
let mut v___x_338_: u32 = 0; 
v___x_338_ = 1;
return v___x_338_;
}
}
}
1 => {
v___x_327_ = l_Expr_count(v_f_325_);
v___x_328_ = l_Expr_count(v_g_326_);
v___x_329_ = lean_uint32_add(v___x_327_, v___x_328_);
return v___x_329_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_count___boxed(mut v_x_339_: *mut lean_object) -> *mut lean_object{
let mut v_res_340_: u32 = 0; let mut v_r_341_: *mut lean_object = core::ptr::null_mut(); 
v_res_340_ = l_Expr_count(v_x_339_);
lean_dec_ref(v_x_339_);
v_r_341_ = lean_box_uint32(v_res_340_);
return v_r_341_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Expr_toString(mut v_x_348_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_348_)
{
0 => {
let mut v_a_349_: *mut lean_object = core::ptr::null_mut(); let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); 
v_a_349_ = lean_ctor_get(v_x_348_, 0);
v___x_350_ = l_Int_repr(v_a_349_);
return v___x_350_;
}
1 => {
let mut v_a_351_: *mut lean_object = core::ptr::null_mut(); 
v_a_351_ = lean_ctor_get(v_x_348_, 0);
lean_inc_ref(v_a_351_);
return v_a_351_;
}
2 => {
let mut v_a_352_: *mut lean_object = core::ptr::null_mut(); let mut v_a_353_: *mut lean_object = core::ptr::null_mut(); let mut v___x_354_: *mut lean_object = core::ptr::null_mut(); let mut v___x_355_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_357_: *mut lean_object = core::ptr::null_mut(); let mut v___x_358_: *mut lean_object = core::ptr::null_mut(); let mut v___x_359_: *mut lean_object = core::ptr::null_mut(); let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); 
v_a_352_ = lean_ctor_get(v_x_348_, 0);
v_a_353_ = lean_ctor_get(v_x_348_, 1);
v___x_354_ = l_Expr_Expr_toString___closed__0;
v___x_355_ = l_Expr_Expr_toString(v_a_352_);
v___x_356_ = lean_string_append(v___x_354_, v___x_355_);
lean_dec_ref(v___x_355_);
v___x_357_ = l_Expr_Expr_toString___closed__1;
v___x_358_ = lean_string_append(v___x_356_, v___x_357_);
v___x_359_ = l_Expr_Expr_toString(v_a_353_);
v___x_360_ = lean_string_append(v___x_358_, v___x_359_);
lean_dec_ref(v___x_359_);
v___x_361_ = l_Expr_Expr_toString___closed__2;
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
return v___x_362_;
}
3 => {
let mut v_a_363_: *mut lean_object = core::ptr::null_mut(); let mut v_a_364_: *mut lean_object = core::ptr::null_mut(); let mut v___x_365_: *mut lean_object = core::ptr::null_mut(); let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); let mut v___x_367_: *mut lean_object = core::ptr::null_mut(); let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); let mut v___x_372_: *mut lean_object = core::ptr::null_mut(); let mut v___x_373_: *mut lean_object = core::ptr::null_mut(); 
v_a_363_ = lean_ctor_get(v_x_348_, 0);
v_a_364_ = lean_ctor_get(v_x_348_, 1);
v___x_365_ = l_Expr_Expr_toString___closed__0;
v___x_366_ = l_Expr_Expr_toString(v_a_363_);
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
lean_dec_ref(v___x_366_);
v___x_368_ = l_Expr_Expr_toString___closed__3;
v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
v___x_370_ = l_Expr_Expr_toString(v_a_364_);
v___x_371_ = lean_string_append(v___x_369_, v___x_370_);
lean_dec_ref(v___x_370_);
v___x_372_ = l_Expr_Expr_toString___closed__2;
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
return v___x_373_;
}
4 => {
let mut v_a_374_: *mut lean_object = core::ptr::null_mut(); let mut v_a_375_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v___x_384_: *mut lean_object = core::ptr::null_mut(); 
v_a_374_ = lean_ctor_get(v_x_348_, 0);
v_a_375_ = lean_ctor_get(v_x_348_, 1);
v___x_376_ = l_Expr_Expr_toString___closed__0;
v___x_377_ = l_Expr_Expr_toString(v_a_374_);
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
lean_dec_ref(v___x_377_);
v___x_379_ = l_Expr_Expr_toString___closed__4;
v___x_380_ = lean_string_append(v___x_378_, v___x_379_);
v___x_381_ = l_Expr_Expr_toString(v_a_375_);
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
lean_dec_ref(v___x_381_);
v___x_383_ = l_Expr_Expr_toString___closed__2;
v___x_384_ = lean_string_append(v___x_382_, v___x_383_);
return v___x_384_;
}
_ => {
let mut v_a_385_: *mut lean_object = core::ptr::null_mut(); let mut v___x_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: *mut lean_object = core::ptr::null_mut(); let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); let mut v___x_389_: *mut lean_object = core::ptr::null_mut(); let mut v___x_390_: *mut lean_object = core::ptr::null_mut(); 
v_a_385_ = lean_ctor_get(v_x_348_, 0);
v___x_386_ = l_Expr_Expr_toString___closed__5;
v___x_387_ = l_Expr_Expr_toString(v_a_385_);
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
lean_dec_ref(v___x_387_);
v___x_389_ = l_Expr_Expr_toString___closed__2;
v___x_390_ = lean_string_append(v___x_388_, v___x_389_);
return v___x_390_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Expr_toString___boxed(mut v_x_391_: *mut lean_object) -> *mut lean_object{
let mut v_res_392_: *mut lean_object = core::ptr::null_mut(); 
v_res_392_ = l_Expr_Expr_toString(v_x_391_);
lean_dec_ref(v_x_391_);
return v_res_392_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_nestAux(mut v_s_395_: *mut lean_object, mut v_f_396_: *mut lean_object, mut v_x_397_: *mut lean_object, mut v_x_398_: *mut lean_object) -> *mut lean_object{
let mut v_zero_400_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_401_: u8 = 0; let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: *mut lean_object = core::ptr::null_mut(); let mut v_a_405_: *mut lean_object = core::ptr::null_mut(); let mut v_one_406_: *mut lean_object = core::ptr::null_mut(); let mut v_n_407_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_400_ = lean_unsigned_to_nat(0);
v_isZero_401_ = lean_nat_dec_eq(v_x_397_, v_zero_400_);
if v_isZero_401_ == 1 {
let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_397_);
lean_dec_ref(v_f_396_);
v___x_402_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_402_, 0, v_x_398_);
return v___x_402_;
} else {
let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: *mut lean_object = core::ptr::null_mut(); 
v___x_403_ = lean_nat_sub(v_s_395_, v_x_397_);
lean_inc_ref(v_f_396_);
v___x_404_ = lean_apply_3(v_f_396_, v___x_403_, v_x_398_, lean_box(0));
if lean_obj_tag(v___x_404_) == 0 {
let mut v_a_405_: *mut lean_object = core::ptr::null_mut(); let mut v_one_406_: *mut lean_object = core::ptr::null_mut(); let mut v_n_407_: *mut lean_object = core::ptr::null_mut(); 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
v_one_406_ = lean_unsigned_to_nat(1);
v_n_407_ = lean_nat_sub(v_x_397_, v_one_406_);
lean_dec(v_x_397_);
v_x_397_ = v_n_407_;
v_x_398_ = v_a_405_;
state = 0; continue;
} else {
lean_dec(v_x_397_);
lean_dec_ref(v_f_396_);
return v___x_404_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_nestAux___boxed(mut v_s_409_: *mut lean_object, mut v_f_410_: *mut lean_object, mut v_x_411_: *mut lean_object, mut v_x_412_: *mut lean_object, mut v_a_413_: *mut lean_object) -> *mut lean_object{
let mut v_res_414_: *mut lean_object = core::ptr::null_mut(); 
v_res_414_ = l_Expr_nestAux(v_s_409_, v_f_410_, v_x_411_, v_x_412_);
lean_dec(v_s_409_);
return v_res_414_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_nest(mut v_f_415_: *mut lean_object, mut v_n_416_: *mut lean_object, mut v_e_417_: *mut lean_object) -> *mut lean_object{
let mut v___x_419_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_n_416_);
v___x_419_ = l_Expr_nestAux(v_n_416_, v_f_415_, v_n_416_, v_e_417_);
lean_dec(v_n_416_);
return v___x_419_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_nest___boxed(mut v_f_420_: *mut lean_object, mut v_n_421_: *mut lean_object, mut v_e_422_: *mut lean_object, mut v_a_423_: *mut lean_object) -> *mut lean_object{
let mut v_res_424_: *mut lean_object = core::ptr::null_mut(); 
v_res_424_ = l_Expr_nest(v_f_420_, v_n_421_, v_e_422_);
return v_res_424_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0(mut v_s_425_: *mut lean_object) -> *mut lean_object{
let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); 
v___x_427_ = lean_get_stdout();
v_putStr_428_ = lean_ctor_get(v___x_427_, 4);
lean_inc_ref(v_putStr_428_);
lean_dec_ref(v___x_427_);
v___x_429_ = lean_apply_2(v_putStr_428_, v_s_425_, lean_box(0));
return v___x_429_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0___boxed(mut v_s_430_: *mut lean_object, mut v_a_431_: *mut lean_object) -> *mut lean_object{
let mut v_res_432_: *mut lean_object = core::ptr::null_mut(); 
v_res_432_ = l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0(v_s_430_);
return v_res_432_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00Expr_deriv_spec__0(mut v_s_433_: *mut lean_object) -> *mut lean_object{
let mut v___x_435_: u32 = 0; let mut v___x_436_: *mut lean_object = core::ptr::null_mut(); let mut v___x_437_: *mut lean_object = core::ptr::null_mut(); 
v___x_435_ = 10;
v___x_436_ = lean_string_push(v_s_433_, v___x_435_);
v___x_437_ = l_IO_print___at___00IO_println___at___00Expr_deriv_spec__0_spec__0(v___x_436_);
return v___x_437_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00Expr_deriv_spec__0___boxed(mut v_s_438_: *mut lean_object, mut v_a_439_: *mut lean_object) -> *mut lean_object{
let mut v_res_440_: *mut lean_object = core::ptr::null_mut(); 
v_res_440_ = l_IO_println___at___00Expr_deriv_spec__0(v_s_438_);
return v_res_440_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_deriv(mut v_i_443_: *mut lean_object, mut v_f_444_: *mut lean_object) -> *mut lean_object{
let mut v___x_446_: *mut lean_object = core::ptr::null_mut(); let mut v_d_447_: *mut lean_object = core::ptr::null_mut(); let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_453_: u32 = 0; let mut v___x_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_460_: u8 = 0; let mut v___x_462_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_463_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_464_: u8 = 0; let mut v_unused_465_: *mut lean_object = core::ptr::null_mut(); let mut v_a_466_: *mut lean_object = core::ptr::null_mut(); let mut v___x_468_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_469_: u8 = 0; let mut v___x_471_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_472_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_473_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_446_ = l_Expr_deriv___closed__0;
v_d_447_ = l_Expr_d(v___x_446_, v_f_444_);
v___x_448_ = lean_unsigned_to_nat(1);
v___x_449_ = lean_nat_add(v_i_443_, v___x_448_);
v___x_450_ = l_Nat_reprFast(v___x_449_);
v___x_451_ = l_Expr_deriv___closed__1;
v___x_452_ = lean_string_append(v___x_450_, v___x_451_);
v___x_453_ = l_Expr_count(v_d_447_);
v___x_454_ = lean_uint32_to_nat(v___x_453_);
v___x_455_ = l_Nat_reprFast(v___x_454_);
v___x_456_ = lean_string_append(v___x_452_, v___x_455_);
lean_dec_ref(v___x_455_);
v___x_457_ = l_IO_println___at___00Expr_deriv_spec__0(v___x_456_);
if lean_obj_tag(v___x_457_) == 0 {
let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_460_: u8 = 0; let mut v_isSharedCheck_464_: u8 = 0; 
v_isSharedCheck_464_ = (!lean_is_exclusive(v___x_457_)) as u8;
if v_isSharedCheck_464_ == 0 {
let mut v_unused_465_: *mut lean_object = core::ptr::null_mut(); 
v_unused_465_ = lean_ctor_get(v___x_457_, 0);
lean_dec(v_unused_465_);
v___x_459_ = v___x_457_;
v_isShared_460_ = v_isSharedCheck_464_;
state = 1; continue;
} else {
lean_dec(v___x_457_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
state = 1; continue;
}
} else {
let mut v_a_466_: *mut lean_object = core::ptr::null_mut(); let mut v___x_468_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_469_: u8 = 0; let mut v_isSharedCheck_473_: u8 = 0; 
lean_dec_ref(v_d_447_);
v_a_466_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_473_ = (!lean_is_exclusive(v___x_457_)) as u8;
if v_isSharedCheck_473_ == 0 {
v___x_468_ = v___x_457_;
v_isShared_469_ = v_isSharedCheck_473_;
state = 3; continue;
} else {
lean_inc(v_a_466_);
lean_dec(v___x_457_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_460_ == 0 {
lean_ctor_set(v___x_459_, 0, v_d_447_);
v___x_462_ = v___x_459_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_463_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_d_447_);
v___x_462_ = v_reuseFailAlloc_463_;
state = 2; continue;
}
}
3 => {
if v_isShared_469_ == 0 {
v___x_471_ = v___x_468_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_472_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_deriv___boxed(mut v_i_474_: *mut lean_object, mut v_f_475_: *mut lean_object, mut v_a_476_: *mut lean_object) -> *mut lean_object{
let mut v_res_477_: *mut lean_object = core::ptr::null_mut(); 
v_res_477_ = l_Expr_deriv(v_i_474_, v_f_475_);
lean_dec(v_i_474_);
return v_res_477_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v_x_480_: *mut lean_object = core::ptr::null_mut(); let mut v_f_481_: *mut lean_object = core::ptr::null_mut(); 
v_x_480_ = l_main___closed__0;
v_f_481_ = l_Expr_pow(v_x_480_, v_x_480_);
return v_f_481_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_483_: u32 = 0; let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); 
v___x_483_ = 1;
v___x_484_ = lean_box_uint32(v___x_483_);
return v___x_484_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__2() -> *mut lean_object{
let mut v___x_485_: u32 = 0; let mut v___x_486_: *mut lean_object = core::ptr::null_mut(); 
v___x_485_ = 0;
v___x_486_ = lean_box_uint32(v___x_485_);
return v___x_486_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_x_487_: *mut lean_object) -> *mut lean_object{
let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v___x_491_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_492_: *mut lean_object = core::ptr::null_mut(); let mut v_head_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); let mut v___x_496_: *mut lean_object = core::ptr::null_mut(); let mut v_n_497_: *mut lean_object = core::ptr::null_mut(); let mut v_f_498_: *mut lean_object = core::ptr::null_mut(); let mut v___x_499_: *mut lean_object = core::ptr::null_mut(); let mut v___x_500_: *mut lean_object = core::ptr::null_mut(); let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_503_: u8 = 0; let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_507_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_508_: u8 = 0; let mut v_unused_509_: *mut lean_object = core::ptr::null_mut(); let mut v_a_510_: *mut lean_object = core::ptr::null_mut(); let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_513_: u8 = 0; let mut v___x_515_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_516_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_517_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_487_) == 1 {
let mut v_tail_492_: *mut lean_object = core::ptr::null_mut(); 
v_tail_492_ = lean_ctor_get(v_x_487_, 1);
if lean_obj_tag(v_tail_492_) == 0 {
let mut v_head_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); let mut v___x_496_: *mut lean_object = core::ptr::null_mut(); let mut v_n_497_: *mut lean_object = core::ptr::null_mut(); let mut v_f_498_: *mut lean_object = core::ptr::null_mut(); let mut v___x_499_: *mut lean_object = core::ptr::null_mut(); let mut v___x_500_: *mut lean_object = core::ptr::null_mut(); 
v_head_493_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_head_493_);
lean_dec_ref_known(v_x_487_, 2);
v___x_494_ = lean_unsigned_to_nat(0);
v___x_495_ = lean_string_utf8_byte_size(v_head_493_);
v___x_496_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_496_, 0, v_head_493_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v_n_497_ = l_String_Slice_toNat_x21(v___x_496_);
lean_dec_ref_known(v___x_496_, 3);
v_f_498_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_499_ = l_main___closed__2;
lean_inc(v_n_497_);
v___x_500_ = l_Expr_nestAux(v_n_497_, v___x_499_, v_n_497_, v_f_498_);
lean_dec(v_n_497_);
if lean_obj_tag(v___x_500_) == 0 {
let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_503_: u8 = 0; let mut v_isSharedCheck_508_: u8 = 0; 
v_isSharedCheck_508_ = (!lean_is_exclusive(v___x_500_)) as u8;
if v_isSharedCheck_508_ == 0 {
let mut v_unused_509_: *mut lean_object = core::ptr::null_mut(); 
v_unused_509_ = lean_ctor_get(v___x_500_, 0);
lean_dec(v_unused_509_);
v___x_502_ = v___x_500_;
v_isShared_503_ = v_isSharedCheck_508_;
state = 2; continue;
} else {
lean_dec(v___x_500_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
state = 2; continue;
}
} else {
let mut v_a_510_: *mut lean_object = core::ptr::null_mut(); let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_513_: u8 = 0; let mut v_isSharedCheck_517_: u8 = 0; 
v_a_510_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_517_ = (!lean_is_exclusive(v___x_500_)) as u8;
if v_isSharedCheck_517_ == 0 {
v___x_512_ = v___x_500_;
v_isShared_513_ = v_isSharedCheck_517_;
state = 4; continue;
} else {
lean_inc(v_a_510_);
lean_dec(v___x_500_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
state = 4; continue;
}
}
} else {
lean_dec_ref_known(v_x_487_, 2);
state = 1; continue;
}
} else {
lean_dec(v_x_487_);
state = 1; continue;
}
}
1 => {
v___x_490_ = l_main___boxed__const__1;
v___x_491_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
2 => {
v___x_504_ = l_main___boxed__const__2;
if v_isShared_503_ == 0 {
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_507_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
state = 3; continue;
}
}
4 => {
if v_isShared_513_ == 0 {
v___x_515_ = v___x_512_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_516_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
state = 5; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_x_518_: *mut lean_object, mut v_a_519_: *mut lean_object) -> *mut lean_object{
let mut v_res_520_: *mut lean_object = core::ptr::null_mut(); 
v_res_520_ = _lean_main(v_x_518_);
return v_res_520_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_deriv(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
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
  let res = initialize_deriv(1 /* builtin */);
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
