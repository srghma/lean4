// Lean compiler output
// Module: const_fold
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mul(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_Expr_mkExpr___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_Expr_mkExpr___closed__0: *mut lean_object = core::ptr::addr_of!(l_Expr_mkExpr___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_toStringAux___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l_Expr_toStringAux___closed__0: *mut lean_object = core::ptr::addr_of!(l_Expr_toStringAux___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_toStringAux___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Expr_toStringAux___closed__1: *mut lean_object = core::ptr::addr_of!(l_Expr_toStringAux___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_toStringAux___closed__2_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 43, 32, 0]};
static mut l_Expr_toStringAux___closed__2: *mut lean_object = core::ptr::addr_of!(l_Expr_toStringAux___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_toStringAux___closed__3_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Expr_toStringAux___closed__3: *mut lean_object = core::ptr::addr_of!(l_Expr_toStringAux___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_Expr_toStringAux___closed__4_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 42, 32, 0]};
static mut l_Expr_toStringAux___closed__4: *mut lean_object = core::ptr::addr_of!(l_Expr_toStringAux___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
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
2 => {
let mut v_a_10_: *mut lean_object = core::ptr::null_mut(); let mut v_a_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); 
v_a_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_a_10_);
v_a_11_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_a_11_);
lean_dec_ref_known(v_t_8_, 2);
v___x_12_ = lean_apply_2(v_k_9_, v_a_10_, v_a_11_);
return v___x_12_;
}
3 => {
let mut v_a_13_: *mut lean_object = core::ptr::null_mut(); let mut v_a_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v_a_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_a_13_);
v_a_14_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_a_14_);
lean_dec_ref_known(v_t_8_, 2);
v___x_15_ = lean_apply_2(v_k_9_, v_a_13_, v_a_14_);
return v___x_15_;
}
_ => {
let mut v_a_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); 
v_a_16_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_a_16_);
lean_dec_ref(v_t_8_);
v___x_17_ = lean_apply_1(v_k_9_, v_a_16_);
return v___x_17_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorElim(mut v_motive_18_: *mut lean_object, mut v_ctorIdx_19_: *mut lean_object, mut v_t_20_: *mut lean_object, mut v_h_21_: *mut lean_object, mut v_k_22_: *mut lean_object) -> *mut lean_object{
let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); 
v___x_23_ = l_Expr_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_ctorElim___boxed(mut v_motive_24_: *mut lean_object, mut v_ctorIdx_25_: *mut lean_object, mut v_t_26_: *mut lean_object, mut v_h_27_: *mut lean_object, mut v_k_28_: *mut lean_object) -> *mut lean_object{
let mut v_res_29_: *mut lean_object = core::ptr::null_mut(); 
v_res_29_ = l_Expr_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Var_elim___redArg(mut v_t_30_: *mut lean_object, mut v_Var_31_: *mut lean_object) -> *mut lean_object{
let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
v___x_32_ = l_Expr_ctorElim___redArg(v_t_30_, v_Var_31_);
return v___x_32_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Var_elim(mut v_motive_33_: *mut lean_object, mut v_t_34_: *mut lean_object, mut v_h_35_: *mut lean_object, mut v_Var_36_: *mut lean_object) -> *mut lean_object{
let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
v___x_37_ = l_Expr_ctorElim___redArg(v_t_34_, v_Var_36_);
return v___x_37_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Val_elim___redArg(mut v_t_38_: *mut lean_object, mut v_Val_39_: *mut lean_object) -> *mut lean_object{
let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_40_ = l_Expr_ctorElim___redArg(v_t_38_, v_Val_39_);
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Val_elim(mut v_motive_41_: *mut lean_object, mut v_t_42_: *mut lean_object, mut v_h_43_: *mut lean_object, mut v_Val_44_: *mut lean_object) -> *mut lean_object{
let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); 
v___x_45_ = l_Expr_ctorElim___redArg(v_t_42_, v_Val_44_);
return v___x_45_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Add_elim___redArg(mut v_t_46_: *mut lean_object, mut v_Add_47_: *mut lean_object) -> *mut lean_object{
let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); 
v___x_48_ = l_Expr_ctorElim___redArg(v_t_46_, v_Add_47_);
return v___x_48_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Add_elim(mut v_motive_49_: *mut lean_object, mut v_t_50_: *mut lean_object, mut v_h_51_: *mut lean_object, mut v_Add_52_: *mut lean_object) -> *mut lean_object{
let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); 
v___x_53_ = l_Expr_ctorElim___redArg(v_t_50_, v_Add_52_);
return v___x_53_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Mul_elim___redArg(mut v_t_54_: *mut lean_object, mut v_Mul_55_: *mut lean_object) -> *mut lean_object{
let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); 
v___x_56_ = l_Expr_ctorElim___redArg(v_t_54_, v_Mul_55_);
return v___x_56_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_Mul_elim(mut v_motive_57_: *mut lean_object, mut v_t_58_: *mut lean_object, mut v_h_59_: *mut lean_object, mut v_Mul_60_: *mut lean_object) -> *mut lean_object{
let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); 
v___x_61_ = l_Expr_ctorElim___redArg(v_t_58_, v_Mul_60_);
return v___x_61_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_mkExpr(mut v_x_64_: *mut lean_object, mut v_x_65_: *mut lean_object) -> *mut lean_object{
let mut v_zero_66_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_67_: u8 = 0; 
v_zero_66_ = lean_unsigned_to_nat(0);
v_isZero_67_ = lean_nat_dec_eq(v_x_64_, v_zero_66_);
if v_isZero_67_ == 1 {
let mut v___x_68_: u8 = 0; 
v___x_68_ = lean_nat_dec_eq(v_x_65_, v_zero_66_);
if v___x_68_ == 0 {
let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); 
v___x_69_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_69_, 0, v_x_65_);
return v___x_69_;
} else {
let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_65_);
v___x_70_ = l_Expr_mkExpr___closed__0;
return v___x_70_;
}
} else {
let mut v_one_71_: *mut lean_object = core::ptr::null_mut(); let mut v_n_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); 
v_one_71_ = lean_unsigned_to_nat(1);
v_n_72_ = lean_nat_sub(v_x_64_, v_one_71_);
v___x_73_ = lean_nat_add(v_x_65_, v_one_71_);
v___x_74_ = l_Expr_mkExpr(v_n_72_, v___x_73_);
v___x_75_ = lean_nat_sub(v_x_65_, v_one_71_);
lean_dec(v_x_65_);
v___x_76_ = l_Expr_mkExpr(v_n_72_, v___x_75_);
lean_dec(v_n_72_);
v___x_77_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_77_, 0, v___x_74_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_mkExpr___boxed(mut v_x_78_: *mut lean_object, mut v_x_79_: *mut lean_object) -> *mut lean_object{
let mut v_res_80_: *mut lean_object = core::ptr::null_mut(); 
v_res_80_ = l_Expr_mkExpr(v_x_78_, v_x_79_);
lean_dec(v_x_78_);
return v_res_80_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_appendAdd(mut v_x_81_: *mut lean_object, mut v_x_82_: *mut lean_object) -> *mut lean_object{
let mut v_a_83_: *mut lean_object = core::ptr::null_mut(); let mut v_a_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_87_: u8 = 0; let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_91_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_92_: u8 = 0; let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_81_) == 2 {
let mut v_a_83_: *mut lean_object = core::ptr::null_mut(); let mut v_a_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_87_: u8 = 0; let mut v_isSharedCheck_92_: u8 = 0; 
v_a_83_ = lean_ctor_get(v_x_81_, 0);
v_a_84_ = lean_ctor_get(v_x_81_, 1);
v_isSharedCheck_92_ = (!lean_is_exclusive(v_x_81_)) as u8;
if v_isSharedCheck_92_ == 0 {
v___x_86_ = v_x_81_;
v_isShared_87_ = v_isSharedCheck_92_;
state = 1; continue;
} else {
lean_inc(v_a_84_);
lean_inc(v_a_83_);
lean_dec(v_x_81_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
state = 1; continue;
}
} else {
let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); 
v___x_93_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v___x_93_, 0, v_x_81_);
lean_ctor_set(v___x_93_, 1, v_x_82_);
return v___x_93_;
}
}
1 => {
v___x_88_ = l_Expr_appendAdd(v_a_84_, v_x_82_);
if v_isShared_87_ == 0 {
lean_ctor_set(v___x_86_, 1, v___x_88_);
v___x_90_ = v___x_86_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_91_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_91_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_83_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_appendMul(mut v_x_94_: *mut lean_object, mut v_x_95_: *mut lean_object) -> *mut lean_object{
let mut v_a_96_: *mut lean_object = core::ptr::null_mut(); let mut v_a_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_100_: u8 = 0; let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_104_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_105_: u8 = 0; let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_94_) == 3 {
let mut v_a_96_: *mut lean_object = core::ptr::null_mut(); let mut v_a_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_100_: u8 = 0; let mut v_isSharedCheck_105_: u8 = 0; 
v_a_96_ = lean_ctor_get(v_x_94_, 0);
v_a_97_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_105_ = (!lean_is_exclusive(v_x_94_)) as u8;
if v_isSharedCheck_105_ == 0 {
v___x_99_ = v_x_94_;
v_isShared_100_ = v_isSharedCheck_105_;
state = 1; continue;
} else {
lean_inc(v_a_97_);
lean_inc(v_a_96_);
lean_dec(v_x_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
state = 1; continue;
}
} else {
let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); 
v___x_106_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v___x_106_, 0, v_x_94_);
lean_ctor_set(v___x_106_, 1, v_x_95_);
return v___x_106_;
}
}
1 => {
v___x_101_ = l_Expr_appendMul(v_a_97_, v_x_95_);
if v_isShared_100_ == 0 {
lean_ctor_set(v___x_99_, 1, v___x_101_);
v___x_103_ = v___x_99_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_104_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_104_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_96_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_reassoc(mut v_x_107_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_107_)
{
2 => {
let mut v_a_108_: *mut lean_object = core::ptr::null_mut(); let mut v_a_109_: *mut lean_object = core::ptr::null_mut(); let mut v_e_u2081_x27_110_: *mut lean_object = core::ptr::null_mut(); let mut v_e_u2082_x27_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); 
v_a_108_ = lean_ctor_get(v_x_107_, 0);
v_a_109_ = lean_ctor_get(v_x_107_, 1);
v_e_u2081_x27_110_ = l_Expr_reassoc(v_a_108_);
v_e_u2082_x27_111_ = l_Expr_reassoc(v_a_109_);
v___x_112_ = l_Expr_appendAdd(v_e_u2081_x27_110_, v_e_u2082_x27_111_);
return v___x_112_;
}
3 => {
let mut v_a_113_: *mut lean_object = core::ptr::null_mut(); let mut v_a_114_: *mut lean_object = core::ptr::null_mut(); let mut v_e_u2081_x27_115_: *mut lean_object = core::ptr::null_mut(); let mut v_e_u2082_x27_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); 
v_a_113_ = lean_ctor_get(v_x_107_, 0);
v_a_114_ = lean_ctor_get(v_x_107_, 1);
v_e_u2081_x27_115_ = l_Expr_reassoc(v_a_113_);
v_e_u2082_x27_116_ = l_Expr_reassoc(v_a_114_);
v___x_117_ = l_Expr_appendMul(v_e_u2081_x27_115_, v_e_u2082_x27_116_);
return v___x_117_;
}
_ => {
lean_inc_ref(v_x_107_);
return v_x_107_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_reassoc___boxed(mut v_x_118_: *mut lean_object) -> *mut lean_object{
let mut v_res_119_: *mut lean_object = core::ptr::null_mut(); 
v_res_119_ = l_Expr_reassoc(v_x_118_);
lean_dec_ref(v_x_118_);
return v_res_119_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_constFolding(mut v_x_120_: *mut lean_object) -> *mut lean_object{
let mut v_a_121_: *mut lean_object = core::ptr::null_mut(); let mut v_a_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_125_: u8 = 0; let mut v_e_u2081_126_: *mut lean_object = core::ptr::null_mut(); let mut v_e_u2082_127_: *mut lean_object = core::ptr::null_mut(); let mut v_a_128_: *mut lean_object = core::ptr::null_mut(); let mut v_a_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_132_: u8 = 0; let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_136_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_137_: u8 = 0; let mut v_a_138_: *mut lean_object = core::ptr::null_mut(); let mut v_a_139_: *mut lean_object = core::ptr::null_mut(); let mut v_a_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_143_: u8 = 0; let mut v_a_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_147_: u8 = 0; let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_153_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_154_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_155_: u8 = 0; let mut v_isSharedCheck_156_: u8 = 0; let mut v_unused_157_: *mut lean_object = core::ptr::null_mut(); let mut v_a_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_161_: u8 = 0; let mut v_a_162_: *mut lean_object = core::ptr::null_mut(); let mut v_a_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_166_: u8 = 0; let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_172_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_173_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_174_: u8 = 0; let mut v_isSharedCheck_175_: u8 = 0; let mut v_unused_176_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_186_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_187_: u8 = 0; let mut v_a_188_: *mut lean_object = core::ptr::null_mut(); let mut v_a_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_192_: u8 = 0; let mut v_e_u2081_193_: *mut lean_object = core::ptr::null_mut(); let mut v_e_u2082_194_: *mut lean_object = core::ptr::null_mut(); let mut v_a_195_: *mut lean_object = core::ptr::null_mut(); let mut v_a_196_: *mut lean_object = core::ptr::null_mut(); let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_199_: u8 = 0; let mut v___x_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_203_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_204_: u8 = 0; let mut v_a_205_: *mut lean_object = core::ptr::null_mut(); let mut v_a_206_: *mut lean_object = core::ptr::null_mut(); let mut v_a_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_210_: u8 = 0; let mut v_a_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_214_: u8 = 0; let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_220_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_221_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_222_: u8 = 0; let mut v_isSharedCheck_223_: u8 = 0; let mut v_unused_224_: *mut lean_object = core::ptr::null_mut(); let mut v_a_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_228_: u8 = 0; let mut v_a_229_: *mut lean_object = core::ptr::null_mut(); let mut v_a_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_232_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_233_: u8 = 0; let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_239_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_240_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_241_: u8 = 0; let mut v_isSharedCheck_242_: u8 = 0; let mut v_unused_243_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_249_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_250_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_253_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_254_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_120_)
{
2 => {
let mut v_a_121_: *mut lean_object = core::ptr::null_mut(); let mut v_a_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_125_: u8 = 0; let mut v_isSharedCheck_187_: u8 = 0; 
v_a_121_ = lean_ctor_get(v_x_120_, 0);
v_a_122_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_187_ = (!lean_is_exclusive(v_x_120_)) as u8;
if v_isSharedCheck_187_ == 0 {
v___x_124_ = v_x_120_;
v_isShared_125_ = v_isSharedCheck_187_;
state = 1; continue;
} else {
lean_inc(v_a_122_);
lean_inc(v_a_121_);
lean_dec(v_x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_187_;
state = 1; continue;
}
}
3 => {
let mut v_a_188_: *mut lean_object = core::ptr::null_mut(); let mut v_a_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_192_: u8 = 0; let mut v_isSharedCheck_254_: u8 = 0; 
v_a_188_ = lean_ctor_get(v_x_120_, 0);
v_a_189_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_254_ = (!lean_is_exclusive(v_x_120_)) as u8;
if v_isSharedCheck_254_ == 0 {
v___x_191_ = v_x_120_;
v_isShared_192_ = v_isSharedCheck_254_;
state = 15; continue;
} else {
lean_inc(v_a_189_);
lean_inc(v_a_188_);
lean_dec(v_x_120_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_254_;
state = 15; continue;
}
}
_ => {
return v_x_120_;
}
}
}
1 => {
v_e_u2081_126_ = l_Expr_constFolding(v_a_121_);
v_e_u2082_127_ = l_Expr_constFolding(v_a_122_);
if lean_obj_tag(v_e_u2081_126_) == 1 {
match lean_obj_tag(v_e_u2082_127_)
{
1 => {
let mut v_a_128_: *mut lean_object = core::ptr::null_mut(); let mut v_a_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_132_: u8 = 0; let mut v_isSharedCheck_137_: u8 = 0; 
lean_del_object(v___x_124_);
v_a_128_ = lean_ctor_get(v_e_u2081_126_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v_e_u2081_126_, 1);
v_a_129_ = lean_ctor_get(v_e_u2082_127_, 0);
v_isSharedCheck_137_ = (!lean_is_exclusive(v_e_u2082_127_)) as u8;
if v_isSharedCheck_137_ == 0 {
v___x_131_ = v_e_u2082_127_;
v_isShared_132_ = v_isSharedCheck_137_;
state = 2; continue;
} else {
lean_inc(v_a_129_);
lean_dec(v_e_u2082_127_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_137_;
state = 2; continue;
}
}
2 => {
let mut v_a_138_: *mut lean_object = core::ptr::null_mut(); 
v_a_138_ = lean_ctor_get(v_e_u2082_127_, 1);
lean_inc_ref(v_a_138_);
if lean_obj_tag(v_a_138_) == 1 {
let mut v_a_139_: *mut lean_object = core::ptr::null_mut(); let mut v_a_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_143_: u8 = 0; let mut v_isSharedCheck_156_: u8 = 0; 
lean_del_object(v___x_124_);
v_a_139_ = lean_ctor_get(v_e_u2081_126_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v_e_u2081_126_, 1);
v_a_140_ = lean_ctor_get(v_e_u2082_127_, 0);
v_isSharedCheck_156_ = (!lean_is_exclusive(v_e_u2082_127_)) as u8;
if v_isSharedCheck_156_ == 0 {
let mut v_unused_157_: *mut lean_object = core::ptr::null_mut(); 
v_unused_157_ = lean_ctor_get(v_e_u2082_127_, 1);
lean_dec(v_unused_157_);
v___x_142_ = v_e_u2082_127_;
v_isShared_143_ = v_isSharedCheck_156_;
state = 4; continue;
} else {
lean_inc(v_a_140_);
lean_dec(v_e_u2082_127_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_156_;
state = 4; continue;
}
} else {
let mut v_a_158_: *mut lean_object = core::ptr::null_mut(); 
v_a_158_ = lean_ctor_get(v_e_u2082_127_, 0);
lean_inc_ref(v_a_158_);
if lean_obj_tag(v_a_158_) == 1 {
let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_161_: u8 = 0; let mut v_isSharedCheck_175_: u8 = 0; 
lean_del_object(v___x_124_);
v_isSharedCheck_175_ = (!lean_is_exclusive(v_e_u2082_127_)) as u8;
if v_isSharedCheck_175_ == 0 {
let mut v_unused_176_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_177_: *mut lean_object = core::ptr::null_mut(); 
v_unused_176_ = lean_ctor_get(v_e_u2082_127_, 1);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_e_u2082_127_, 0);
lean_dec(v_unused_177_);
v___x_160_ = v_e_u2082_127_;
v_isShared_161_ = v_isSharedCheck_175_;
state = 8; continue;
} else {
lean_dec(v_e_u2082_127_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_175_;
state = 8; continue;
}
} else {
let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_a_158_);
lean_dec_ref(v_a_138_);
if v_isShared_125_ == 0 {
lean_ctor_set(v___x_124_, 1, v_e_u2082_127_);
lean_ctor_set(v___x_124_, 0, v_e_u2081_126_);
v___x_179_ = v___x_124_;
state = 12; continue;
} else {
let mut v_reuseFailAlloc_180_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_180_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_e_u2081_126_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_e_u2082_127_);
v___x_179_ = v_reuseFailAlloc_180_;
state = 12; continue;
}
}
}
}
_ => {
let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_125_ == 0 {
lean_ctor_set(v___x_124_, 1, v_e_u2082_127_);
lean_ctor_set(v___x_124_, 0, v_e_u2081_126_);
v___x_182_ = v___x_124_;
state = 13; continue;
} else {
let mut v_reuseFailAlloc_183_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_183_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_e_u2081_126_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_e_u2082_127_);
v___x_182_ = v_reuseFailAlloc_183_;
state = 13; continue;
}
}
}
} else {
let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_125_ == 0 {
lean_ctor_set(v___x_124_, 1, v_e_u2082_127_);
lean_ctor_set(v___x_124_, 0, v_e_u2081_126_);
v___x_185_ = v___x_124_;
state = 14; continue;
} else {
let mut v_reuseFailAlloc_186_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_186_ = lean_alloc_ctor(2, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_e_u2081_126_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_e_u2082_127_);
v___x_185_ = v_reuseFailAlloc_186_;
state = 14; continue;
}
}
}
15 => {
v_e_u2081_193_ = l_Expr_constFolding(v_a_188_);
v_e_u2082_194_ = l_Expr_constFolding(v_a_189_);
if lean_obj_tag(v_e_u2081_193_) == 1 {
match lean_obj_tag(v_e_u2082_194_)
{
1 => {
let mut v_a_195_: *mut lean_object = core::ptr::null_mut(); let mut v_a_196_: *mut lean_object = core::ptr::null_mut(); let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_199_: u8 = 0; let mut v_isSharedCheck_204_: u8 = 0; 
lean_del_object(v___x_191_);
v_a_195_ = lean_ctor_get(v_e_u2081_193_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v_e_u2081_193_, 1);
v_a_196_ = lean_ctor_get(v_e_u2082_194_, 0);
v_isSharedCheck_204_ = (!lean_is_exclusive(v_e_u2082_194_)) as u8;
if v_isSharedCheck_204_ == 0 {
v___x_198_ = v_e_u2082_194_;
v_isShared_199_ = v_isSharedCheck_204_;
state = 16; continue;
} else {
lean_inc(v_a_196_);
lean_dec(v_e_u2082_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
state = 16; continue;
}
}
3 => {
let mut v_a_205_: *mut lean_object = core::ptr::null_mut(); 
v_a_205_ = lean_ctor_get(v_e_u2082_194_, 1);
lean_inc_ref(v_a_205_);
if lean_obj_tag(v_a_205_) == 1 {
let mut v_a_206_: *mut lean_object = core::ptr::null_mut(); let mut v_a_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_210_: u8 = 0; let mut v_isSharedCheck_223_: u8 = 0; 
lean_del_object(v___x_191_);
v_a_206_ = lean_ctor_get(v_e_u2081_193_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v_e_u2081_193_, 1);
v_a_207_ = lean_ctor_get(v_e_u2082_194_, 0);
v_isSharedCheck_223_ = (!lean_is_exclusive(v_e_u2082_194_)) as u8;
if v_isSharedCheck_223_ == 0 {
let mut v_unused_224_: *mut lean_object = core::ptr::null_mut(); 
v_unused_224_ = lean_ctor_get(v_e_u2082_194_, 1);
lean_dec(v_unused_224_);
v___x_209_ = v_e_u2082_194_;
v_isShared_210_ = v_isSharedCheck_223_;
state = 18; continue;
} else {
lean_inc(v_a_207_);
lean_dec(v_e_u2082_194_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_223_;
state = 18; continue;
}
} else {
let mut v_a_225_: *mut lean_object = core::ptr::null_mut(); 
v_a_225_ = lean_ctor_get(v_e_u2082_194_, 0);
lean_inc_ref(v_a_225_);
if lean_obj_tag(v_a_225_) == 1 {
let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_228_: u8 = 0; let mut v_isSharedCheck_242_: u8 = 0; 
lean_del_object(v___x_191_);
v_isSharedCheck_242_ = (!lean_is_exclusive(v_e_u2082_194_)) as u8;
if v_isSharedCheck_242_ == 0 {
let mut v_unused_243_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_244_: *mut lean_object = core::ptr::null_mut(); 
v_unused_243_ = lean_ctor_get(v_e_u2082_194_, 1);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_e_u2082_194_, 0);
lean_dec(v_unused_244_);
v___x_227_ = v_e_u2082_194_;
v_isShared_228_ = v_isSharedCheck_242_;
state = 22; continue;
} else {
lean_dec(v_e_u2082_194_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_242_;
state = 22; continue;
}
} else {
let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_a_225_);
lean_dec_ref(v_a_205_);
if v_isShared_192_ == 0 {
lean_ctor_set(v___x_191_, 1, v_e_u2082_194_);
lean_ctor_set(v___x_191_, 0, v_e_u2081_193_);
v___x_246_ = v___x_191_;
state = 26; continue;
} else {
let mut v_reuseFailAlloc_247_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_247_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_e_u2081_193_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_e_u2082_194_);
v___x_246_ = v_reuseFailAlloc_247_;
state = 26; continue;
}
}
}
}
_ => {
let mut v___x_249_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_192_ == 0 {
lean_ctor_set(v___x_191_, 1, v_e_u2082_194_);
lean_ctor_set(v___x_191_, 0, v_e_u2081_193_);
v___x_249_ = v___x_191_;
state = 27; continue;
} else {
let mut v_reuseFailAlloc_250_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_250_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_e_u2081_193_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_e_u2082_194_);
v___x_249_ = v_reuseFailAlloc_250_;
state = 27; continue;
}
}
}
} else {
let mut v___x_252_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_192_ == 0 {
lean_ctor_set(v___x_191_, 1, v_e_u2082_194_);
lean_ctor_set(v___x_191_, 0, v_e_u2081_193_);
v___x_252_ = v___x_191_;
state = 28; continue;
} else {
let mut v_reuseFailAlloc_253_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_253_ = lean_alloc_ctor(3, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_e_u2081_193_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_e_u2082_194_);
v___x_252_ = v_reuseFailAlloc_253_;
state = 28; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_size(mut v_x_255_: *mut lean_object) -> *mut lean_object{
let mut v_l_257_: *mut lean_object = core::ptr::null_mut(); let mut v_r_258_: *mut lean_object = core::ptr::null_mut(); let mut v___x_259_: *mut lean_object = core::ptr::null_mut(); let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_261_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v_a_264_: *mut lean_object = core::ptr::null_mut(); let mut v_a_265_: *mut lean_object = core::ptr::null_mut(); let mut v_a_266_: *mut lean_object = core::ptr::null_mut(); let mut v_a_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_255_)
{
2 => {
let mut v_a_264_: *mut lean_object = core::ptr::null_mut(); let mut v_a_265_: *mut lean_object = core::ptr::null_mut(); 
v_a_264_ = lean_ctor_get(v_x_255_, 0);
v_a_265_ = lean_ctor_get(v_x_255_, 1);
v_l_257_ = v_a_264_;
v_r_258_ = v_a_265_;
state = 1; continue;
}
3 => {
let mut v_a_266_: *mut lean_object = core::ptr::null_mut(); let mut v_a_267_: *mut lean_object = core::ptr::null_mut(); 
v_a_266_ = lean_ctor_get(v_x_255_, 0);
v_a_267_ = lean_ctor_get(v_x_255_, 1);
v_l_257_ = v_a_266_;
v_r_258_ = v_a_267_;
state = 1; continue;
}
_ => {
let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); 
v___x_268_ = lean_unsigned_to_nat(1);
return v___x_268_;
}
}
}
1 => {
v___x_259_ = l_Expr_size(v_l_257_);
v___x_260_ = l_Expr_size(v_r_258_);
v___x_261_ = lean_nat_add(v___x_259_, v___x_260_);
lean_dec(v___x_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_unsigned_to_nat(1);
v___x_263_ = lean_nat_add(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
return v___x_263_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_size___boxed(mut v_x_269_: *mut lean_object) -> *mut lean_object{
let mut v_res_270_: *mut lean_object = core::ptr::null_mut(); 
v_res_270_ = l_Expr_size(v_x_269_);
lean_dec_ref(v_x_269_);
return v_res_270_;
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_toStringAux(mut v_x_276_: *mut lean_object, mut v_x_277_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_276_)
{
0 => {
let mut v_a_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_279_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: *mut lean_object = core::ptr::null_mut(); let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); 
v_a_278_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v_x_276_, 1);
v___x_279_ = l_Expr_toStringAux___closed__0;
v___x_280_ = lean_string_append(v_x_277_, v___x_279_);
v___x_281_ = l_Nat_reprFast(v_a_278_);
v___x_282_ = lean_string_append(v___x_280_, v___x_281_);
lean_dec_ref(v___x_281_);
return v___x_282_;
}
1 => {
let mut v_a_283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_285_: *mut lean_object = core::ptr::null_mut(); 
v_a_283_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v_x_276_, 1);
v___x_284_ = l_Nat_reprFast(v_a_283_);
v___x_285_ = lean_string_append(v_x_277_, v___x_284_);
lean_dec_ref(v___x_284_);
return v___x_285_;
}
2 => {
let mut v_a_286_: *mut lean_object = core::ptr::null_mut(); let mut v_a_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); let mut v___x_295_: *mut lean_object = core::ptr::null_mut(); 
v_a_286_ = lean_ctor_get(v_x_276_, 0);
lean_inc_ref(v_a_286_);
v_a_287_ = lean_ctor_get(v_x_276_, 1);
lean_inc_ref(v_a_287_);
lean_dec_ref_known(v_x_276_, 2);
v___x_288_ = l_Expr_toStringAux___closed__1;
v___x_289_ = lean_string_append(v_x_277_, v___x_288_);
v___x_290_ = l_Expr_toStringAux(v_a_286_, v___x_289_);
v___x_291_ = l_Expr_toStringAux___closed__2;
v___x_292_ = lean_string_append(v___x_290_, v___x_291_);
v___x_293_ = l_Expr_toStringAux(v_a_287_, v___x_292_);
v___x_294_ = l_Expr_toStringAux___closed__3;
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
return v___x_295_;
}
_ => {
let mut v_a_296_: *mut lean_object = core::ptr::null_mut(); let mut v_a_297_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); 
v_a_296_ = lean_ctor_get(v_x_276_, 0);
lean_inc_ref(v_a_296_);
v_a_297_ = lean_ctor_get(v_x_276_, 1);
lean_inc_ref(v_a_297_);
lean_dec_ref_known(v_x_276_, 2);
v___x_298_ = l_Expr_toStringAux___closed__1;
v___x_299_ = lean_string_append(v_x_277_, v___x_298_);
v___x_300_ = l_Expr_toStringAux(v_a_296_, v___x_299_);
v___x_301_ = l_Expr_toStringAux___closed__4;
v___x_302_ = lean_string_append(v___x_300_, v___x_301_);
v___x_303_ = l_Expr_toStringAux(v_a_297_, v___x_302_);
v___x_304_ = l_Expr_toStringAux___closed__3;
v___x_305_ = lean_string_append(v___x_303_, v___x_304_);
return v___x_305_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_eval(mut v_x_306_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_306_)
{
0 => {
let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); 
v___x_307_ = lean_unsigned_to_nat(0);
return v___x_307_;
}
1 => {
let mut v_a_308_: *mut lean_object = core::ptr::null_mut(); 
v_a_308_ = lean_ctor_get(v_x_306_, 0);
lean_inc(v_a_308_);
return v_a_308_;
}
2 => {
let mut v_a_309_: *mut lean_object = core::ptr::null_mut(); let mut v_a_310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_312_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); 
v_a_309_ = lean_ctor_get(v_x_306_, 0);
v_a_310_ = lean_ctor_get(v_x_306_, 1);
v___x_311_ = l_Expr_eval(v_a_309_);
v___x_312_ = l_Expr_eval(v_a_310_);
v___x_313_ = lean_nat_add(v___x_311_, v___x_312_);
lean_dec(v___x_312_);
lean_dec(v___x_311_);
return v___x_313_;
}
_ => {
let mut v_a_314_: *mut lean_object = core::ptr::null_mut(); let mut v_a_315_: *mut lean_object = core::ptr::null_mut(); let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); let mut v___x_318_: *mut lean_object = core::ptr::null_mut(); 
v_a_314_ = lean_ctor_get(v_x_306_, 0);
v_a_315_ = lean_ctor_get(v_x_306_, 1);
v___x_316_ = l_Expr_eval(v_a_314_);
v___x_317_ = l_Expr_eval(v_a_315_);
v___x_318_ = lean_nat_mul(v___x_316_, v___x_317_);
lean_dec(v___x_317_);
lean_dec(v___x_316_);
return v___x_318_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Expr_eval___boxed(mut v_x_319_: *mut lean_object) -> *mut lean_object{
let mut v_res_320_: *mut lean_object = core::ptr::null_mut(); 
v_res_320_ = l_Expr_eval(v_x_319_);
lean_dec_ref(v_x_319_);
return v_res_320_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_321_: *mut lean_object) -> *mut lean_object{
let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_324_: *mut lean_object = core::ptr::null_mut(); let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); 
v___x_323_ = lean_get_stdout();
v_putStr_324_ = lean_ctor_get(v___x_323_, 4);
lean_inc_ref(v_putStr_324_);
lean_dec_ref(v___x_323_);
v___x_325_ = lean_apply_2(v_putStr_324_, v_s_321_, lean_box(0));
return v___x_325_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_326_: *mut lean_object, mut v_a_327_: *mut lean_object) -> *mut lean_object{
let mut v_res_328_: *mut lean_object = core::ptr::null_mut(); 
v_res_328_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_326_);
return v_res_328_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_329_: *mut lean_object) -> *mut lean_object{
let mut v___x_331_: u32 = 0; let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); 
v___x_331_ = 10;
v___x_332_ = lean_string_push(v_s_329_, v___x_331_);
v___x_333_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_332_);
return v___x_333_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_334_: *mut lean_object, mut v_a_335_: *mut lean_object) -> *mut lean_object{
let mut v_res_336_: *mut lean_object = core::ptr::null_mut(); 
v_res_336_ = l_IO_println___at___00main_spec__0(v_s_334_);
return v_res_336_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_338_: u32 = 0; let mut v___x_339_: *mut lean_object = core::ptr::null_mut(); 
v___x_338_ = 1;
v___x_339_ = lean_box_uint32(v___x_338_);
return v___x_339_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__2() -> *mut lean_object{
let mut v___x_340_: u32 = 0; let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); 
v___x_340_ = 0;
v___x_341_ = lean_box_uint32(v___x_340_);
return v___x_341_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_x_342_: *mut lean_object) -> *mut lean_object{
let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_347_: *mut lean_object = core::ptr::null_mut(); let mut v_head_348_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v_n_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_353_: *mut lean_object = core::ptr::null_mut(); let mut v_e_354_: *mut lean_object = core::ptr::null_mut(); let mut v_v_u2081_355_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_357_: *mut lean_object = core::ptr::null_mut(); let mut v_v_u2082_358_: *mut lean_object = core::ptr::null_mut(); let mut v___x_359_: *mut lean_object = core::ptr::null_mut(); let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: *mut lean_object = core::ptr::null_mut(); let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_367_: u8 = 0; let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_371_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_372_: u8 = 0; let mut v_unused_373_: *mut lean_object = core::ptr::null_mut(); let mut v_a_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_377_: u8 = 0; let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_380_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_381_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_342_) == 1 {
let mut v_tail_347_: *mut lean_object = core::ptr::null_mut(); 
v_tail_347_ = lean_ctor_get(v_x_342_, 1);
if lean_obj_tag(v_tail_347_) == 0 {
let mut v_head_348_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v_n_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_353_: *mut lean_object = core::ptr::null_mut(); let mut v_e_354_: *mut lean_object = core::ptr::null_mut(); let mut v_v_u2081_355_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_357_: *mut lean_object = core::ptr::null_mut(); let mut v_v_u2082_358_: *mut lean_object = core::ptr::null_mut(); let mut v___x_359_: *mut lean_object = core::ptr::null_mut(); let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: *mut lean_object = core::ptr::null_mut(); let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); 
v_head_348_ = lean_ctor_get(v_x_342_, 0);
lean_inc(v_head_348_);
lean_dec_ref_known(v_x_342_, 2);
v___x_349_ = lean_unsigned_to_nat(0);
v___x_350_ = lean_string_utf8_byte_size(v_head_348_);
v___x_351_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_351_, 0, v_head_348_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
v_n_352_ = l_String_Slice_toNat_x21(v___x_351_);
lean_dec_ref_known(v___x_351_, 3);
v___x_353_ = lean_unsigned_to_nat(1);
v_e_354_ = l_Expr_mkExpr(v_n_352_, v___x_353_);
lean_dec(v_n_352_);
v_v_u2081_355_ = l_Expr_eval(v_e_354_);
v___x_356_ = l_Expr_reassoc(v_e_354_);
lean_dec_ref(v_e_354_);
v___x_357_ = l_Expr_constFolding(v___x_356_);
v_v_u2082_358_ = l_Expr_eval(v___x_357_);
lean_dec_ref(v___x_357_);
v___x_359_ = l_Nat_reprFast(v_v_u2081_355_);
v___x_360_ = l_main___closed__0;
v___x_361_ = lean_string_append(v___x_359_, v___x_360_);
v___x_362_ = l_Nat_reprFast(v_v_u2082_358_);
v___x_363_ = lean_string_append(v___x_361_, v___x_362_);
lean_dec_ref(v___x_362_);
v___x_364_ = l_IO_println___at___00main_spec__0(v___x_363_);
if lean_obj_tag(v___x_364_) == 0 {
let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_367_: u8 = 0; let mut v_isSharedCheck_372_: u8 = 0; 
v_isSharedCheck_372_ = (!lean_is_exclusive(v___x_364_)) as u8;
if v_isSharedCheck_372_ == 0 {
let mut v_unused_373_: *mut lean_object = core::ptr::null_mut(); 
v_unused_373_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_373_);
v___x_366_ = v___x_364_;
v_isShared_367_ = v_isSharedCheck_372_;
state = 2; continue;
} else {
lean_dec(v___x_364_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
state = 2; continue;
}
} else {
let mut v_a_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_377_: u8 = 0; let mut v_isSharedCheck_381_: u8 = 0; 
v_a_374_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = (!lean_is_exclusive(v___x_364_)) as u8;
if v_isSharedCheck_381_ == 0 {
v___x_376_ = v___x_364_;
v_isShared_377_ = v_isSharedCheck_381_;
state = 4; continue;
} else {
lean_inc(v_a_374_);
lean_dec(v___x_364_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
state = 4; continue;
}
}
} else {
lean_dec_ref_known(v_x_342_, 2);
state = 1; continue;
}
} else {
lean_dec(v_x_342_);
state = 1; continue;
}
}
1 => {
v___x_345_ = l_main___boxed__const__1;
v___x_346_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
2 => {
v___x_368_ = l_main___boxed__const__2;
if v_isShared_367_ == 0 {
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_370_ = v___x_366_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_371_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
state = 3; continue;
}
}
4 => {
if v_isShared_377_ == 0 {
v___x_379_ = v___x_376_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_380_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
state = 5; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_x_382_: *mut lean_object, mut v_a_383_: *mut lean_object) -> *mut lean_object{
let mut v_res_384_: *mut lean_object = core::ptr::null_mut(); 
v_res_384_ = _lean_main(v_x_382_);
return v_res_384_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_const__fold(builtin: u8) -> *mut lean_object {
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
  let res = initialize_const__fold(1 /* builtin */);
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
