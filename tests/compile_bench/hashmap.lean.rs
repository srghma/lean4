// Lean compiler output
// Module: hashmap
// Imports: public import Init public meta import Init public import Std.Data.HashMap public import Std.Data.Iterators public import Std.Data.HashSet public import Std.Data.HashSet.Iterator
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_mk_array(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_add(_: u64, _: u64) -> u64;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_shift_right(_: u64, _: u64) -> u64;
    fn lean_uint64_xor(_: u64, _: u64) -> u64;
    fn lean_uint64_to_usize(_: u64) -> usize;
    fn lean_usize_of_nat(_: *mut lean_object) -> usize;
    fn lean_usize_sub(_: usize, _: usize) -> usize;
    fn lean_usize_land(_: usize, _: usize) -> usize;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_uint64_dec_eq(_: u64, _: u64) -> u8;
    fn lean_array_uset(_: *mut lean_object, _: usize, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mul(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_div(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_fget(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fset(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_mul(_: u64, _: u64) -> u64;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_nextPowerOfTwo(_: *mut lean_object) -> *mut lean_object;
    fn lean_io_mono_nanos_now() -> *mut lean_object;
    fn lean_float_of_nat(_: *mut lean_object) -> f64;
    fn lean_float_div(_: f64, _: f64) -> f64;
    fn lean_uint64_of_nat(_: *mut lean_object) -> u64;
    fn l_List_lengthTR___redArg(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_size(_: *mut lean_object) -> usize;
    fn lean_usize_dec_lt(_: usize, _: usize) -> u8;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn l_List_get_x21Internal___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn l_mkPanicMessageWithDecl(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    static mut l_instInhabitedError: *mut lean_object;
    fn l_instInhabitedEIO___aux__1___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_panic_fn_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_float_to_string(_: f64) -> *mut lean_object;
    fn lean_float_decLt(_: f64, _: f64) -> u8;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static mut l_REP: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_benchIterate___boxed__const__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*0 + 8) as u16, m_other: 0, m_tag: 0 }, m_objs: [0 as *mut lean_object] };
#[no_mangle] pub static mut l_benchIterate___boxed__const__1: *mut lean_object = core::ptr::addr_of!(l_benchIterate___boxed__const__1_value) as *mut lean_object;
#[no_mangle] pub static mut l_testPrimes: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_iterRandM___redArg(mut v_seed_1_: u64) -> u64{
return v_seed_1_;
}
#[no_mangle] pub unsafe extern "C" fn l_iterRandM___redArg___boxed(mut v_seed_2_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_3_: u64 = 0; let mut v_res_4_: u64 = 0; let mut v_r_5_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_3_ = lean_unbox_uint64(v_seed_2_);
lean_dec_ref(v_seed_2_);
v_res_4_ = l_iterRandM___redArg(v_seed_boxed_3_);
v_r_5_ = lean_box_uint64(v_res_4_);
return v_r_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_iterRandM(mut v_m_6_: *mut lean_object, mut v_seed_7_: u64) -> u64{
return v_seed_7_;
}
#[no_mangle] pub unsafe extern "C" fn l_iterRandM___boxed(mut v_m_8_: *mut lean_object, mut v_seed_9_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_10_: u64 = 0; let mut v_res_11_: u64 = 0; let mut v_r_12_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_10_ = lean_unbox_uint64(v_seed_9_);
lean_dec_ref(v_seed_9_);
v_res_11_ = l_iterRandM(v_m_8_, v_seed_boxed_10_);
v_r_12_ = lean_box_uint64(v_res_11_);
return v_r_12_;
}
#[no_mangle] pub unsafe extern "C" fn l_iterRand(mut v_seed_13_: u64) -> u64{
return v_seed_13_;
}
#[no_mangle] pub unsafe extern "C" fn l_iterRand___boxed(mut v_seed_14_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_15_: u64 = 0; let mut v_res_16_: u64 = 0; let mut v_r_17_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_15_ = lean_unbox_uint64(v_seed_14_);
lean_dec_ref(v_seed_14_);
v_res_16_ = l_iterRand(v_seed_boxed_15_);
v_r_17_ = lean_box_uint64(v_res_16_);
return v_r_17_;
}
#[no_mangle] pub unsafe extern "C" fn l_instIteratorRandomIteratorUInt64OfPure___redArg___lam__0(mut v_inst_18_: *mut lean_object, mut v_x_19_: u64) -> *mut lean_object{
let mut v___x_20_: u64 = 0; let mut v___x_21_: u64 = 0; let mut v___x_22_: u64 = 0; let mut v___x_23_: u64 = 0; let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); 
v___x_20_ = 1u64;
v___x_21_ = lean_uint64_add(v_x_19_, v___x_20_);
v___x_22_ = 3787392781u64;
v___x_23_ = lean_uint64_mul(v___x_21_, v___x_22_);
v___x_24_ = lean_box_uint64(v___x_23_);
v___x_25_ = lean_box_uint64(v_x_19_);
v___x_26_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_26_, 0, v___x_24_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v___x_27_ = lean_apply_2(v_inst_18_, lean_box(0), v___x_26_);
return v___x_27_;
}
#[no_mangle] pub unsafe extern "C" fn l_instIteratorRandomIteratorUInt64OfPure___redArg___lam__0___boxed(mut v_inst_28_: *mut lean_object, mut v_x_29_: *mut lean_object) -> *mut lean_object{
let mut v_x_78__boxed_30_: u64 = 0; let mut v_res_31_: *mut lean_object = core::ptr::null_mut(); 
v_x_78__boxed_30_ = lean_unbox_uint64(v_x_29_);
lean_dec_ref(v_x_29_);
v_res_31_ = l_instIteratorRandomIteratorUInt64OfPure___redArg___lam__0(v_inst_28_, v_x_78__boxed_30_);
return v_res_31_;
}
#[no_mangle] pub unsafe extern "C" fn l_instIteratorRandomIteratorUInt64OfPure___redArg(mut v_inst_32_: *mut lean_object) -> *mut lean_object{
let mut v___f_33_: *mut lean_object = core::ptr::null_mut(); 
v___f_33_ = lean_alloc_closure(l_instIteratorRandomIteratorUInt64OfPure___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_33_, 0, v_inst_32_);
return v___f_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_instIteratorRandomIteratorUInt64OfPure(mut v_m_34_: *mut lean_object, mut v_inst_35_: *mut lean_object) -> *mut lean_object{
let mut v___f_36_: *mut lean_object = core::ptr::null_mut(); 
v___f_36_ = lean_alloc_closure(l_instIteratorRandomIteratorUInt64OfPure___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_36_, 0, v_inst_35_);
return v___f_36_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1_spec__2_spec__4___redArg(mut v_x_37_: *mut lean_object, mut v_x_38_: *mut lean_object) -> *mut lean_object{
let mut v_key_39_: *mut lean_object = core::ptr::null_mut(); let mut v_value_40_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_44_: u8 = 0; let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: u64 = 0; let mut v___x_47_: u64 = 0; let mut v___x_48_: u64 = 0; let mut v___x_49_: u64 = 0; let mut v_fold_50_: u64 = 0; let mut v___x_51_: u64 = 0; let mut v___x_52_: u64 = 0; let mut v___x_53_: u64 = 0; let mut v___x_54_: usize = 0; let mut v___x_55_: usize = 0; let mut v___x_56_: usize = 0; let mut v___x_57_: usize = 0; let mut v___x_58_: usize = 0; let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_64_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_65_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_38_) == 0 {
return v_x_37_;
} else {
let mut v_key_39_: *mut lean_object = core::ptr::null_mut(); let mut v_value_40_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_44_: u8 = 0; let mut v_isSharedCheck_65_: u8 = 0; 
v_key_39_ = lean_ctor_get(v_x_38_, 0);
v_value_40_ = lean_ctor_get(v_x_38_, 1);
v_tail_41_ = lean_ctor_get(v_x_38_, 2);
v_isSharedCheck_65_ = (!lean_is_exclusive(v_x_38_)) as u8;
if v_isSharedCheck_65_ == 0 {
v___x_43_ = v_x_38_;
v_isShared_44_ = v_isSharedCheck_65_;
state = 1; continue;
} else {
lean_inc(v_tail_41_);
lean_inc(v_value_40_);
lean_inc(v_key_39_);
lean_dec(v_x_38_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_65_;
state = 1; continue;
}
}
}
1 => {
v___x_45_ = lean_array_get_size(v_x_37_);
v___x_46_ = 32u64;
v___x_47_ = lean_unbox_uint64(v_key_39_);
v___x_48_ = lean_uint64_shift_right(v___x_47_, v___x_46_);
v___x_49_ = lean_unbox_uint64(v_key_39_);
v_fold_50_ = lean_uint64_xor(v___x_49_, v___x_48_);
v___x_51_ = 16u64;
v___x_52_ = lean_uint64_shift_right(v_fold_50_, v___x_51_);
v___x_53_ = lean_uint64_xor(v_fold_50_, v___x_52_);
v___x_54_ = lean_uint64_to_usize(v___x_53_);
v___x_55_ = lean_usize_of_nat(v___x_45_);
v___x_56_ = 1usize;
v___x_57_ = lean_usize_sub(v___x_55_, v___x_56_);
v___x_58_ = lean_usize_land(v___x_54_, v___x_57_);
v___x_59_ = lean_array_uget_borrowed(v_x_37_, v___x_58_);
lean_inc(v___x_59_);
if v_isShared_44_ == 0 {
lean_ctor_set(v___x_43_, 2, v___x_59_);
v___x_61_ = v___x_43_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_64_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_key_39_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_value_40_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v___x_59_);
v___x_61_ = v_reuseFailAlloc_64_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1_spec__2___redArg(mut v_i_66_: *mut lean_object, mut v_source_67_: *mut lean_object, mut v_target_68_: *mut lean_object) -> *mut lean_object{
let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: u8 = 0; let mut v_es_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v_source_73_: *mut lean_object = core::ptr::null_mut(); let mut v_target_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_69_ = lean_array_get_size(v_source_67_);
v___x_70_ = lean_nat_dec_lt(v_i_66_, v___x_69_);
if v___x_70_ == 0 {
lean_dec_ref(v_source_67_);
lean_dec(v_i_66_);
return v_target_68_;
} else {
let mut v_es_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v_source_73_: *mut lean_object = core::ptr::null_mut(); let mut v_target_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); 
v_es_71_ = lean_array_fget(v_source_67_, v_i_66_);
v___x_72_ = lean_box(0);
v_source_73_ = lean_array_fset(v_source_67_, v_i_66_, v___x_72_);
v_target_74_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1_spec__2_spec__4___redArg(v_target_68_, v_es_71_);
v___x_75_ = lean_unsigned_to_nat(1);
v___x_76_ = lean_nat_add(v_i_66_, v___x_75_);
lean_dec(v_i_66_);
v_i_66_ = v___x_76_;
v_source_67_ = v_source_73_;
v_target_68_ = v_target_74_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1___redArg(mut v_data_78_: *mut lean_object) -> *mut lean_object{
let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v_nbuckets_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); 
v___x_79_ = lean_array_get_size(v_data_78_);
v___x_80_ = lean_unsigned_to_nat(2);
v_nbuckets_81_ = lean_nat_mul(v___x_79_, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(0);
v___x_83_ = lean_box(0);
v___x_84_ = lean_mk_array(v_nbuckets_81_, v___x_83_);
v___x_85_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1_spec__2___redArg(v___x_82_, v_data_78_, v___x_84_);
return v___x_85_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2___redArg(mut v_a_86_: u64, mut v_b_87_: *mut lean_object, mut v_x_88_: *mut lean_object) -> *mut lean_object{
let mut v_key_89_: *mut lean_object = core::ptr::null_mut(); let mut v_value_90_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_94_: u8 = 0; let mut v___x_95_: u64 = 0; let mut v___x_96_: u8 = 0; let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_104_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_105_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_88_) == 0 {
lean_dec(v_b_87_);
return v_x_88_;
} else {
let mut v_key_89_: *mut lean_object = core::ptr::null_mut(); let mut v_value_90_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_94_: u8 = 0; let mut v_isSharedCheck_105_: u8 = 0; 
v_key_89_ = lean_ctor_get(v_x_88_, 0);
v_value_90_ = lean_ctor_get(v_x_88_, 1);
v_tail_91_ = lean_ctor_get(v_x_88_, 2);
v_isSharedCheck_105_ = (!lean_is_exclusive(v_x_88_)) as u8;
if v_isSharedCheck_105_ == 0 {
v___x_93_ = v_x_88_;
v_isShared_94_ = v_isSharedCheck_105_;
state = 1; continue;
} else {
lean_inc(v_tail_91_);
lean_inc(v_value_90_);
lean_inc(v_key_89_);
lean_dec(v_x_88_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_105_;
state = 1; continue;
}
}
}
1 => {
v___x_95_ = lean_unbox_uint64(v_key_89_);
v___x_96_ = lean_uint64_dec_eq(v___x_95_, v_a_86_);
if v___x_96_ == 0 {
let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); 
v___x_97_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2___redArg(v_a_86_, v_b_87_, v_tail_91_);
if v_isShared_94_ == 0 {
lean_ctor_set(v___x_93_, 2, v___x_97_);
v___x_99_ = v___x_93_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_100_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_key_89_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_value_90_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
state = 2; continue;
}
} else {
let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_value_90_);
lean_dec(v_key_89_);
v___x_101_ = lean_box_uint64(v_a_86_);
if v_isShared_94_ == 0 {
lean_ctor_set(v___x_93_, 1, v_b_87_);
lean_ctor_set(v___x_93_, 0, v___x_101_);
v___x_103_ = v___x_93_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_104_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_b_87_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v_tail_91_);
v___x_103_ = v_reuseFailAlloc_104_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2___redArg___boxed(mut v_a_106_: *mut lean_object, mut v_b_107_: *mut lean_object, mut v_x_108_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_109_: u64 = 0; let mut v_res_110_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_109_ = lean_unbox_uint64(v_a_106_);
lean_dec_ref(v_a_106_);
v_res_110_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2___redArg(v_a_boxed_109_, v_b_107_, v_x_108_);
return v_res_110_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(mut v_a_111_: u64, mut v_x_112_: *mut lean_object) -> u8{
let mut v___x_113_: u8 = 0; let mut v_key_114_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: u64 = 0; let mut v___x_117_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_112_) == 0 {
let mut v___x_113_: u8 = 0; 
v___x_113_ = 0;
return v___x_113_;
} else {
let mut v_key_114_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: u64 = 0; let mut v___x_117_: u8 = 0; 
v_key_114_ = lean_ctor_get(v_x_112_, 0);
v_tail_115_ = lean_ctor_get(v_x_112_, 2);
v___x_116_ = lean_unbox_uint64(v_key_114_);
v___x_117_ = lean_uint64_dec_eq(v___x_116_, v_a_111_);
if v___x_117_ == 0 {
v_x_112_ = v_tail_115_;
state = 0; continue;
} else {
return v___x_117_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___redArg___boxed(mut v_a_119_: *mut lean_object, mut v_x_120_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_121_: u64 = 0; let mut v_res_122_: u8 = 0; let mut v_r_123_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_121_ = lean_unbox_uint64(v_a_119_);
lean_dec_ref(v_a_119_);
v_res_122_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_a_boxed_121_, v_x_120_);
lean_dec(v_x_120_);
v_r_123_ = lean_box((v_res_122_) as usize);
return v_r_123_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0___redArg(mut v_m_124_: *mut lean_object, mut v_a_125_: u64, mut v_b_126_: *mut lean_object) -> *mut lean_object{
let mut v_size_127_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_131_: u8 = 0; let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: u64 = 0; let mut v___x_134_: u64 = 0; let mut v_fold_135_: u64 = 0; let mut v___x_136_: u64 = 0; let mut v___x_137_: u64 = 0; let mut v___x_138_: u64 = 0; let mut v___x_139_: usize = 0; let mut v___x_140_: usize = 0; let mut v___x_141_: usize = 0; let mut v___x_142_: usize = 0; let mut v___x_143_: usize = 0; let mut v_bkt_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: u8 = 0; let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v_size_x27_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_x27_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: u8 = 0; let mut v_val_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_x27_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_170_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_171_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_size_127_ = lean_ctor_get(v_m_124_, 0);
v_buckets_128_ = lean_ctor_get(v_m_124_, 1);
v_isSharedCheck_171_ = (!lean_is_exclusive(v_m_124_)) as u8;
if v_isSharedCheck_171_ == 0 {
v___x_130_ = v_m_124_;
v_isShared_131_ = v_isSharedCheck_171_;
state = 1; continue;
} else {
lean_inc(v_buckets_128_);
lean_inc(v_size_127_);
lean_dec(v_m_124_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_171_;
state = 1; continue;
}
}
1 => {
v___x_132_ = lean_array_get_size(v_buckets_128_);
v___x_133_ = 32u64;
v___x_134_ = lean_uint64_shift_right(v_a_125_, v___x_133_);
v_fold_135_ = lean_uint64_xor(v_a_125_, v___x_134_);
v___x_136_ = 16u64;
v___x_137_ = lean_uint64_shift_right(v_fold_135_, v___x_136_);
v___x_138_ = lean_uint64_xor(v_fold_135_, v___x_137_);
v___x_139_ = lean_uint64_to_usize(v___x_138_);
v___x_140_ = lean_usize_of_nat(v___x_132_);
v___x_141_ = 1usize;
v___x_142_ = lean_usize_sub(v___x_140_, v___x_141_);
v___x_143_ = lean_usize_land(v___x_139_, v___x_142_);
v_bkt_144_ = lean_array_uget_borrowed(v_buckets_128_, v___x_143_);
v___x_145_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_a_125_, v_bkt_144_);
if v___x_145_ == 0 {
let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v_size_x27_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_x27_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: u8 = 0; 
v___x_146_ = lean_unsigned_to_nat(1);
v_size_x27_147_ = lean_nat_add(v_size_127_, v___x_146_);
lean_dec(v_size_127_);
v___x_148_ = lean_box_uint64(v_a_125_);
lean_inc(v_bkt_144_);
v___x_149_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_b_126_);
lean_ctor_set(v___x_149_, 2, v_bkt_144_);
v_buckets_x27_150_ = lean_array_uset(v_buckets_128_, v___x_143_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(4);
v___x_152_ = lean_nat_mul(v_size_x27_147_, v___x_151_);
v___x_153_ = lean_unsigned_to_nat(3);
v___x_154_ = lean_nat_div(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_array_get_size(v_buckets_x27_150_);
v___x_156_ = lean_nat_dec_le(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
if v___x_156_ == 0 {
let mut v_val_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); 
v_val_157_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1___redArg(v_buckets_x27_150_);
if v_isShared_131_ == 0 {
lean_ctor_set(v___x_130_, 1, v_val_157_);
lean_ctor_set(v___x_130_, 0, v_size_x27_147_);
v___x_159_ = v___x_130_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_160_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_size_x27_147_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_val_157_);
v___x_159_ = v_reuseFailAlloc_160_;
state = 2; continue;
}
} else {
let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_131_ == 0 {
lean_ctor_set(v___x_130_, 1, v_buckets_x27_150_);
lean_ctor_set(v___x_130_, 0, v_size_x27_147_);
v___x_162_ = v___x_130_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_163_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_size_x27_147_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_buckets_x27_150_);
v___x_162_ = v_reuseFailAlloc_163_;
state = 3; continue;
}
}
} else {
let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_x27_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_bkt_144_);
v___x_164_ = lean_box(0);
v_buckets_x27_165_ = lean_array_uset(v_buckets_128_, v___x_143_, v___x_164_);
v___x_166_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2___redArg(v_a_125_, v_b_126_, v_bkt_144_);
v___x_167_ = lean_array_uset(v_buckets_x27_165_, v___x_143_, v___x_166_);
if v_isShared_131_ == 0 {
lean_ctor_set(v___x_130_, 1, v___x_167_);
v___x_169_ = v___x_130_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_170_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_size_127_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
state = 4; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0___redArg___boxed(mut v_m_172_: *mut lean_object, mut v_a_173_: *mut lean_object, mut v_b_174_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_175_: u64 = 0; let mut v_res_176_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_175_ = lean_unbox_uint64(v_a_173_);
lean_dec_ref(v_a_173_);
v_res_176_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0___redArg(v_m_172_, v_a_boxed_175_, v_b_174_);
return v_res_176_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mkMapWithCap_spec__1___redArg(mut v_a_177_: *mut lean_object, mut v_b_178_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_179_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_183_: u8 = 0; let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: u8 = 0; let mut v___x_186_: u64 = 0; let mut v___x_187_: u64 = 0; let mut v___x_188_: u64 = 0; let mut v___x_189_: u64 = 0; let mut v___x_190_: u64 = 0; let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); let mut v___x_195_: u64 = 0; let mut v___x_196_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_198_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_199_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_179_ = lean_ctor_get(v_a_177_, 0);
v_inner_180_ = lean_ctor_get(v_a_177_, 1);
v_isSharedCheck_199_ = (!lean_is_exclusive(v_a_177_)) as u8;
if v_isSharedCheck_199_ == 0 {
v___x_182_ = v_a_177_;
v_isShared_183_ = v_isSharedCheck_199_;
state = 1; continue;
} else {
lean_inc(v_inner_180_);
lean_inc(v_countdown_179_);
lean_dec(v_a_177_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_199_;
state = 1; continue;
}
}
1 => {
v___x_184_ = lean_unsigned_to_nat(1);
v___x_185_ = lean_nat_dec_eq(v_countdown_179_, v___x_184_);
if v___x_185_ == 0 {
let mut v___x_186_: u64 = 0; let mut v___x_187_: u64 = 0; let mut v___x_188_: u64 = 0; let mut v___x_189_: u64 = 0; let mut v___x_190_: u64 = 0; let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); 
v___x_186_ = 1u64;
v___x_187_ = lean_unbox_uint64(v_inner_180_);
v___x_188_ = lean_uint64_add(v___x_187_, v___x_186_);
v___x_189_ = 3787392781u64;
v___x_190_ = lean_uint64_mul(v___x_188_, v___x_189_);
v___x_191_ = lean_nat_sub(v_countdown_179_, v___x_184_);
lean_dec(v_countdown_179_);
v___x_192_ = lean_box_uint64(v___x_190_);
if v_isShared_183_ == 0 {
lean_ctor_set(v___x_182_, 1, v___x_192_);
lean_ctor_set(v___x_182_, 0, v___x_191_);
v___x_194_ = v___x_182_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_198_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_192_);
v___x_194_ = v_reuseFailAlloc_198_;
state = 2; continue;
}
} else {
lean_del_object(v___x_182_);
lean_dec(v_inner_180_);
lean_dec(v_countdown_179_);
return v_b_178_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mkMapWithCap(mut v_seed_200_: u64, mut v_size_201_: *mut lean_object) -> *mut lean_object{
let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); let mut v___x_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v_map_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); 
v___x_202_ = lean_unsigned_to_nat(0);
v___x_203_ = lean_unsigned_to_nat(4);
v___x_204_ = lean_nat_mul(v_size_201_, v___x_203_);
v___x_205_ = lean_unsigned_to_nat(3);
v___x_206_ = lean_nat_div(v___x_204_, v___x_205_);
lean_dec(v___x_204_);
v___x_207_ = l_Nat_nextPowerOfTwo(v___x_206_);
lean_dec(v___x_206_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_mk_array(v___x_207_, v___x_208_);
v_map_210_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_map_210_, 0, v___x_202_);
lean_ctor_set(v_map_210_, 1, v___x_209_);
v___x_211_ = lean_unsigned_to_nat(1);
v___x_212_ = lean_nat_add(v_size_201_, v___x_211_);
v___x_213_ = lean_box_uint64(v_seed_200_);
v___x_214_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = l_WellFounded_opaqueFix_u2083___at___00mkMapWithCap_spec__1___redArg(v___x_214_, v_map_210_);
return v___x_215_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkMapWithCap___boxed(mut v_seed_216_: *mut lean_object, mut v_size_217_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_218_: u64 = 0; let mut v_res_219_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_218_ = lean_unbox_uint64(v_seed_216_);
lean_dec_ref(v_seed_216_);
v_res_219_ = l_mkMapWithCap(v_seed_boxed_218_, v_size_217_);
lean_dec(v_size_217_);
return v_res_219_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0(mut v_00_u03b2_220_: *mut lean_object, mut v_m_221_: *mut lean_object, mut v_a_222_: u64, mut v_b_223_: *mut lean_object) -> *mut lean_object{
let mut v___x_224_: *mut lean_object = core::ptr::null_mut(); 
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0___redArg(v_m_221_, v_a_222_, v_b_223_);
return v___x_224_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0___boxed(mut v_00_u03b2_225_: *mut lean_object, mut v_m_226_: *mut lean_object, mut v_a_227_: *mut lean_object, mut v_b_228_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_229_: u64 = 0; let mut v_res_230_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_229_ = lean_unbox_uint64(v_a_227_);
lean_dec_ref(v_a_227_);
v_res_230_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0(v_00_u03b2_225_, v_m_226_, v_a_boxed_229_, v_b_228_);
return v_res_230_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mkMapWithCap_spec__1(mut v_inst_231_: *mut lean_object, mut v_R_232_: *mut lean_object, mut v_a_233_: *mut lean_object, mut v_b_234_: *mut lean_object, mut v_c_235_: *mut lean_object) -> *mut lean_object{
let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); 
v___x_236_ = l_WellFounded_opaqueFix_u2083___at___00mkMapWithCap_spec__1___redArg(v_a_233_, v_b_234_);
return v___x_236_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0(mut v_00_u03b2_237_: *mut lean_object, mut v_a_238_: u64, mut v_x_239_: *mut lean_object) -> u8{
let mut v___x_240_: u8 = 0; 
v___x_240_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_a_238_, v_x_239_);
return v___x_240_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___boxed(mut v_00_u03b2_241_: *mut lean_object, mut v_a_242_: *mut lean_object, mut v_x_243_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_244_: u64 = 0; let mut v_res_245_: u8 = 0; let mut v_r_246_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_244_ = lean_unbox_uint64(v_a_242_);
lean_dec_ref(v_a_242_);
v_res_245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0(v_00_u03b2_241_, v_a_boxed_244_, v_x_243_);
lean_dec(v_x_243_);
v_r_246_ = lean_box((v_res_245_) as usize);
return v_r_246_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1(mut v_00_u03b2_247_: *mut lean_object, mut v_data_248_: *mut lean_object) -> *mut lean_object{
let mut v___x_249_: *mut lean_object = core::ptr::null_mut(); 
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1___redArg(v_data_248_);
return v___x_249_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2(mut v_00_u03b2_250_: *mut lean_object, mut v_a_251_: u64, mut v_b_252_: *mut lean_object, mut v_x_253_: *mut lean_object) -> *mut lean_object{
let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); 
v___x_254_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2___redArg(v_a_251_, v_b_252_, v_x_253_);
return v___x_254_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2___boxed(mut v_00_u03b2_255_: *mut lean_object, mut v_a_256_: *mut lean_object, mut v_b_257_: *mut lean_object, mut v_x_258_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_259_: u64 = 0; let mut v_res_260_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_259_ = lean_unbox_uint64(v_a_256_);
lean_dec_ref(v_a_256_);
v_res_260_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__2(v_00_u03b2_255_, v_a_boxed_259_, v_b_257_, v_x_258_);
return v_res_260_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1_spec__2(mut v_00_u03b2_261_: *mut lean_object, mut v_i_262_: *mut lean_object, mut v_source_263_: *mut lean_object, mut v_target_264_: *mut lean_object) -> *mut lean_object{
let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); 
v___x_265_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1_spec__2___redArg(v_i_262_, v_source_263_, v_target_264_);
return v___x_265_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1_spec__2_spec__4(mut v_00_u03b2_266_: *mut lean_object, mut v_x_267_: *mut lean_object, mut v_x_268_: *mut lean_object) -> *mut lean_object{
let mut v___x_269_: *mut lean_object = core::ptr::null_mut(); 
v___x_269_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1_spec__2_spec__4___redArg(v_x_267_, v_x_268_);
return v___x_269_;
}
#[no_mangle] pub unsafe extern "C" fn l_timeNanos(mut v_reps_270_: *mut lean_object, mut v_x_271_: *mut lean_object) -> *mut lean_object{
let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_277_: u8 = 0; let mut v___x_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_279_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: f64 = 0.0; let mut v___x_281_: f64 = 0.0; let mut v___x_282_: f64 = 0.0; let mut v___x_283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_285_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_286_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_287_: u8 = 0; let mut v_unused_288_: *mut lean_object = core::ptr::null_mut(); let mut v_a_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_292_: u8 = 0; let mut v___x_294_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_295_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_296_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_273_ = lean_io_mono_nanos_now();
v___x_274_ = lean_apply_1(v_x_271_, lean_box(0));
if lean_obj_tag(v___x_274_) == 0 {
let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_277_: u8 = 0; let mut v_isSharedCheck_287_: u8 = 0; 
v_isSharedCheck_287_ = (!lean_is_exclusive(v___x_274_)) as u8;
if v_isSharedCheck_287_ == 0 {
let mut v_unused_288_: *mut lean_object = core::ptr::null_mut(); 
v_unused_288_ = lean_ctor_get(v___x_274_, 0);
lean_dec(v_unused_288_);
v___x_276_ = v___x_274_;
v_isShared_277_ = v_isSharedCheck_287_;
state = 1; continue;
} else {
lean_dec(v___x_274_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_287_;
state = 1; continue;
}
} else {
let mut v_a_289_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_292_: u8 = 0; let mut v_isSharedCheck_296_: u8 = 0; 
lean_dec(v___x_273_);
lean_dec(v_reps_270_);
v_a_289_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_296_ = (!lean_is_exclusive(v___x_274_)) as u8;
if v_isSharedCheck_296_ == 0 {
v___x_291_ = v___x_274_;
v_isShared_292_ = v_isSharedCheck_296_;
state = 3; continue;
} else {
lean_inc(v_a_289_);
lean_dec(v___x_274_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
state = 3; continue;
}
}
}
1 => {
v___x_278_ = lean_io_mono_nanos_now();
v___x_279_ = lean_nat_sub(v___x_278_, v___x_273_);
lean_dec(v___x_273_);
lean_dec(v___x_278_);
v___x_280_ = lean_float_of_nat(v___x_279_);
v___x_281_ = lean_float_of_nat(v_reps_270_);
v___x_282_ = lean_float_div(v___x_280_, v___x_281_);
v___x_283_ = lean_box_float(v___x_282_);
if v_isShared_277_ == 0 {
lean_ctor_set(v___x_276_, 0, v___x_283_);
v___x_285_ = v___x_276_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_286_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
state = 2; continue;
}
}
3 => {
if v_isShared_292_ == 0 {
v___x_294_ = v___x_291_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_295_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_timeNanos___boxed(mut v_reps_297_: *mut lean_object, mut v_x_298_: *mut lean_object, mut v_a_299_: *mut lean_object) -> *mut lean_object{
let mut v_res_300_: *mut lean_object = core::ptr::null_mut(); 
v_res_300_ = l_timeNanos(v_reps_297_, v_x_298_);
return v_res_300_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_REP() -> *mut lean_object{
let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); 
v___x_301_ = lean_unsigned_to_nat(100);
return v___x_301_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00benchContainsHit_spec__0___redArg(mut v_m_302_: *mut lean_object, mut v_a_303_: u64) -> u8{
let mut v_buckets_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_306_: u64 = 0; let mut v___x_307_: u64 = 0; let mut v_fold_308_: u64 = 0; let mut v___x_309_: u64 = 0; let mut v___x_310_: u64 = 0; let mut v___x_311_: u64 = 0; let mut v___x_312_: usize = 0; let mut v___x_313_: usize = 0; let mut v___x_314_: usize = 0; let mut v___x_315_: usize = 0; let mut v___x_316_: usize = 0; let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); let mut v___x_318_: u8 = 0; 
v_buckets_304_ = lean_ctor_get(v_m_302_, 1);
v___x_305_ = lean_array_get_size(v_buckets_304_);
v___x_306_ = 32u64;
v___x_307_ = lean_uint64_shift_right(v_a_303_, v___x_306_);
v_fold_308_ = lean_uint64_xor(v_a_303_, v___x_307_);
v___x_309_ = 16u64;
v___x_310_ = lean_uint64_shift_right(v_fold_308_, v___x_309_);
v___x_311_ = lean_uint64_xor(v_fold_308_, v___x_310_);
v___x_312_ = lean_uint64_to_usize(v___x_311_);
v___x_313_ = lean_usize_of_nat(v___x_305_);
v___x_314_ = 1usize;
v___x_315_ = lean_usize_sub(v___x_313_, v___x_314_);
v___x_316_ = lean_usize_land(v___x_312_, v___x_315_);
v___x_317_ = lean_array_uget_borrowed(v_buckets_304_, v___x_316_);
v___x_318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_a_303_, v___x_317_);
return v___x_318_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00benchContainsHit_spec__0___redArg___boxed(mut v_m_319_: *mut lean_object, mut v_a_320_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_321_: u64 = 0; let mut v_res_322_: u8 = 0; let mut v_r_323_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_321_ = lean_unbox_uint64(v_a_320_);
lean_dec_ref(v_a_320_);
v_res_322_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00benchContainsHit_spec__0___redArg(v_m_319_, v_a_boxed_321_);
lean_dec_ref(v_m_319_);
v_r_323_ = lean_box((v_res_322_) as usize);
return v_r_323_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg(mut v_map_324_: *mut lean_object, mut v_a_325_: *mut lean_object, mut v_b_326_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_328_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_329_: *mut lean_object = core::ptr::null_mut(); let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_332_: u8 = 0; let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: u8 = 0; let mut v___x_335_: u64 = 0; let mut v___x_336_: u64 = 0; let mut v___x_337_: u64 = 0; let mut v___x_338_: u64 = 0; let mut v___x_339_: u8 = 0; let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_344_: u64 = 0; let mut v___x_345_: u64 = 0; let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_351_: *mut lean_object = core::ptr::null_mut(); let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_353_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_328_ = lean_ctor_get(v_a_325_, 0);
v_inner_329_ = lean_ctor_get(v_a_325_, 1);
v_isSharedCheck_353_ = (!lean_is_exclusive(v_a_325_)) as u8;
if v_isSharedCheck_353_ == 0 {
v___x_331_ = v_a_325_;
v_isShared_332_ = v_isSharedCheck_353_;
state = 1; continue;
} else {
lean_inc(v_inner_329_);
lean_inc(v_countdown_328_);
lean_dec(v_a_325_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_353_;
state = 1; continue;
}
}
1 => {
v___x_333_ = lean_unsigned_to_nat(1);
v___x_334_ = lean_nat_dec_eq(v_countdown_328_, v___x_333_);
if v___x_334_ == 0 {
let mut v___x_335_: u64 = 0; let mut v___x_336_: u64 = 0; let mut v___x_337_: u64 = 0; let mut v___x_338_: u64 = 0; let mut v___x_339_: u8 = 0; 
v___x_335_ = 1u64;
v___x_336_ = lean_unbox_uint64(v_inner_329_);
v___x_337_ = lean_uint64_add(v___x_336_, v___x_335_);
v___x_338_ = lean_unbox_uint64(v_inner_329_);
lean_dec(v_inner_329_);
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00benchContainsHit_spec__0___redArg(v_map_324_, v___x_338_);
if v___x_339_ == 0 {
let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_331_);
lean_dec(v_countdown_328_);
v___x_340_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_341_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
} else {
let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_344_: u64 = 0; let mut v___x_345_: u64 = 0; let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); 
v___x_343_ = lean_box(0);
v___x_344_ = 3787392781u64;
v___x_345_ = lean_uint64_mul(v___x_337_, v___x_344_);
v___x_346_ = lean_nat_sub(v_countdown_328_, v___x_333_);
lean_dec(v_countdown_328_);
v___x_347_ = lean_box_uint64(v___x_345_);
if v_isShared_332_ == 0 {
lean_ctor_set(v___x_331_, 1, v___x_347_);
lean_ctor_set(v___x_331_, 0, v___x_346_);
v___x_349_ = v___x_331_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_351_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_347_);
v___x_349_ = v_reuseFailAlloc_351_;
state = 2; continue;
}
}
} else {
let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_331_);
lean_dec(v_inner_329_);
lean_dec(v_countdown_328_);
v___x_352_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_352_, 0, v_b_326_);
return v___x_352_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg___boxed(mut v_map_354_: *mut lean_object, mut v_a_355_: *mut lean_object, mut v_b_356_: *mut lean_object, mut v___y_357_: *mut lean_object) -> *mut lean_object{
let mut v_res_358_: *mut lean_object = core::ptr::null_mut(); 
v_res_358_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg(v_map_354_, v_a_355_, v_b_356_);
lean_dec_ref(v_map_354_);
return v_res_358_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg(mut v_seed_359_: u64, mut v_size_360_: *mut lean_object, mut v_map_361_: *mut lean_object, mut v_a_362_: *mut lean_object) -> *mut lean_object{
let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); let mut v___x_365_: u8 = 0; let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); let mut v___x_367_: *mut lean_object = core::ptr::null_mut(); let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); let mut v___x_372_: *mut lean_object = core::ptr::null_mut(); let mut v_a_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_377_: u8 = 0; let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_380_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_381_: u8 = 0; let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_364_ = lean_unsigned_to_nat(0);
v___x_365_ = lean_nat_dec_eq(v_a_362_, v___x_364_);
if v___x_365_ == 0 {
let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); let mut v___x_367_: *mut lean_object = core::ptr::null_mut(); let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); 
v___x_366_ = lean_unsigned_to_nat(1);
v___x_367_ = lean_nat_add(v_size_360_, v___x_366_);
v___x_368_ = lean_box_uint64(v_seed_359_);
v___x_369_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = lean_box(0);
v___x_371_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg(v_map_361_, v___x_369_, v___x_370_);
if lean_obj_tag(v___x_371_) == 0 {
let mut v___x_372_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_371_, 1);
v___x_372_ = lean_nat_sub(v_a_362_, v_size_360_);
lean_dec(v_a_362_);
v_a_362_ = v___x_372_;
state = 0; continue;
} else {
let mut v_a_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_377_: u8 = 0; let mut v_isSharedCheck_381_: u8 = 0; 
lean_dec(v_a_362_);
v_a_374_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_381_ = (!lean_is_exclusive(v___x_371_)) as u8;
if v_isSharedCheck_381_ == 0 {
v___x_376_ = v___x_371_;
v_isShared_377_ = v_isSharedCheck_381_;
state = 1; continue;
} else {
lean_inc(v_a_374_);
lean_dec(v___x_371_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
state = 1; continue;
}
}
} else {
let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); 
v___x_382_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_382_, 0, v_a_362_);
return v___x_382_;
}
}
1 => {
if v_isShared_377_ == 0 {
v___x_379_ = v___x_376_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_380_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg___boxed(mut v_seed_383_: *mut lean_object, mut v_size_384_: *mut lean_object, mut v_map_385_: *mut lean_object, mut v_a_386_: *mut lean_object, mut v___y_387_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_388_: u64 = 0; let mut v_res_389_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_388_ = lean_unbox_uint64(v_seed_383_);
lean_dec_ref(v_seed_383_);
v_res_389_ = l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg(v_seed_boxed_388_, v_size_384_, v_map_385_, v_a_386_);
lean_dec_ref(v_map_385_);
lean_dec(v_size_384_);
return v_res_389_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsHit___lam__0(mut v_seed_390_: u64, mut v_size_391_: *mut lean_object, mut v_map_392_: *mut lean_object, mut v_todo_393_: *mut lean_object) -> *mut lean_object{
let mut v___x_395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_397_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_398_: u8 = 0; let mut v___x_399_: *mut lean_object = core::ptr::null_mut(); let mut v___x_401_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_402_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_403_: u8 = 0; let mut v_unused_404_: *mut lean_object = core::ptr::null_mut(); let mut v_a_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_408_: u8 = 0; let mut v___x_410_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_411_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_412_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_395_ = l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg(v_seed_390_, v_size_391_, v_map_392_, v_todo_393_);
if lean_obj_tag(v___x_395_) == 0 {
let mut v___x_397_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_398_: u8 = 0; let mut v_isSharedCheck_403_: u8 = 0; 
v_isSharedCheck_403_ = (!lean_is_exclusive(v___x_395_)) as u8;
if v_isSharedCheck_403_ == 0 {
let mut v_unused_404_: *mut lean_object = core::ptr::null_mut(); 
v_unused_404_ = lean_ctor_get(v___x_395_, 0);
lean_dec(v_unused_404_);
v___x_397_ = v___x_395_;
v_isShared_398_ = v_isSharedCheck_403_;
state = 1; continue;
} else {
lean_dec(v___x_395_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
state = 1; continue;
}
} else {
let mut v_a_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_408_: u8 = 0; let mut v_isSharedCheck_412_: u8 = 0; 
v_a_405_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_412_ = (!lean_is_exclusive(v___x_395_)) as u8;
if v_isSharedCheck_412_ == 0 {
v___x_407_ = v___x_395_;
v_isShared_408_ = v_isSharedCheck_412_;
state = 3; continue;
} else {
lean_inc(v_a_405_);
lean_dec(v___x_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
state = 3; continue;
}
}
}
1 => {
v___x_399_ = lean_box(0);
if v_isShared_398_ == 0 {
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_402_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
state = 2; continue;
}
}
3 => {
if v_isShared_408_ == 0 {
v___x_410_ = v___x_407_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_411_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsHit___lam__0___boxed(mut v_seed_413_: *mut lean_object, mut v_size_414_: *mut lean_object, mut v_map_415_: *mut lean_object, mut v_todo_416_: *mut lean_object, mut v___y_417_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_418_: u64 = 0; let mut v_res_419_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_418_ = lean_unbox_uint64(v_seed_413_);
lean_dec_ref(v_seed_413_);
v_res_419_ = l_benchContainsHit___lam__0(v_seed_boxed_418_, v_size_414_, v_map_415_, v_todo_416_);
lean_dec_ref(v_map_415_);
lean_dec(v_size_414_);
return v_res_419_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsHit(mut v_seed_420_: u64, mut v_size_421_: *mut lean_object) -> *mut lean_object{
let mut v_map_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_424_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_425_: *mut lean_object = core::ptr::null_mut(); let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v___f_427_: *mut lean_object = core::ptr::null_mut(); let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); 
v_map_423_ = l_mkMapWithCap(v_seed_420_, v_size_421_);
v___x_424_ = lean_unsigned_to_nat(100);
v_todo_425_ = lean_nat_mul(v_size_421_, v___x_424_);
v___x_426_ = lean_box_uint64(v_seed_420_);
lean_inc(v_todo_425_);
v___f_427_ = lean_alloc_closure(l_benchContainsHit___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
lean_closure_set(v___f_427_, 0, v___x_426_);
lean_closure_set(v___f_427_, 1, v_size_421_);
lean_closure_set(v___f_427_, 2, v_map_423_);
lean_closure_set(v___f_427_, 3, v_todo_425_);
v___x_428_ = l_timeNanos(v_todo_425_, v___f_427_);
return v___x_428_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsHit___boxed(mut v_seed_429_: *mut lean_object, mut v_size_430_: *mut lean_object, mut v_a_431_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_432_: u64 = 0; let mut v_res_433_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_432_ = lean_unbox_uint64(v_seed_429_);
lean_dec_ref(v_seed_429_);
v_res_433_ = l_benchContainsHit(v_seed_boxed_432_, v_size_430_);
return v_res_433_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00benchContainsHit_spec__0(mut v_00_u03b2_434_: *mut lean_object, mut v_m_435_: *mut lean_object, mut v_a_436_: u64) -> u8{
let mut v___x_437_: u8 = 0; 
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00benchContainsHit_spec__0___redArg(v_m_435_, v_a_436_);
return v___x_437_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00benchContainsHit_spec__0___boxed(mut v_00_u03b2_438_: *mut lean_object, mut v_m_439_: *mut lean_object, mut v_a_440_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_441_: u64 = 0; let mut v_res_442_: u8 = 0; let mut v_r_443_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_441_ = lean_unbox_uint64(v_a_440_);
lean_dec_ref(v_a_440_);
v_res_442_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00benchContainsHit_spec__0(v_00_u03b2_438_, v_m_439_, v_a_boxed_441_);
lean_dec_ref(v_m_439_);
v_r_443_ = lean_box((v_res_442_) as usize);
return v_r_443_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1(mut v_map_444_: *mut lean_object, mut v_inst_445_: *mut lean_object, mut v_R_446_: *mut lean_object, mut v_a_447_: *mut lean_object, mut v_b_448_: *mut lean_object, mut v_c_449_: *mut lean_object) -> *mut lean_object{
let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); 
v___x_451_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg(v_map_444_, v_a_447_, v_b_448_);
return v___x_451_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___boxed(mut v_map_452_: *mut lean_object, mut v_inst_453_: *mut lean_object, mut v_R_454_: *mut lean_object, mut v_a_455_: *mut lean_object, mut v_b_456_: *mut lean_object, mut v_c_457_: *mut lean_object, mut v___y_458_: *mut lean_object) -> *mut lean_object{
let mut v_res_459_: *mut lean_object = core::ptr::null_mut(); 
v_res_459_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1(v_map_452_, v_inst_453_, v_R_454_, v_a_455_, v_b_456_, v_c_457_);
lean_dec_ref(v_map_452_);
return v_res_459_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2(mut v_seed_460_: u64, mut v_size_461_: *mut lean_object, mut v_map_462_: *mut lean_object, mut v_inst_463_: *mut lean_object, mut v_a_464_: *mut lean_object) -> *mut lean_object{
let mut v___x_466_: *mut lean_object = core::ptr::null_mut(); 
v___x_466_ = l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg(v_seed_460_, v_size_461_, v_map_462_, v_a_464_);
return v___x_466_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___boxed(mut v_seed_467_: *mut lean_object, mut v_size_468_: *mut lean_object, mut v_map_469_: *mut lean_object, mut v_inst_470_: *mut lean_object, mut v_a_471_: *mut lean_object, mut v___y_472_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_473_: u64 = 0; let mut v_res_474_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_473_ = lean_unbox_uint64(v_seed_467_);
lean_dec_ref(v_seed_467_);
v_res_474_ = l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2(v_seed_boxed_473_, v_size_468_, v_map_469_, v_inst_470_, v_a_471_);
lean_dec_ref(v_map_469_);
lean_dec(v_size_468_);
return v_res_474_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg(mut v_map_475_: *mut lean_object, mut v_a_476_: *mut lean_object, mut v_b_477_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_479_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_480_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_483_: u8 = 0; let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); let mut v___x_485_: u8 = 0; let mut v_remaining_486_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_489_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_490_: u8 = 0; let mut v___x_491_: u64 = 0; let mut v___x_492_: u64 = 0; let mut v___x_493_: u64 = 0; let mut v___x_494_: u64 = 0; let mut v___x_495_: u64 = 0; let mut v_zero_496_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_497_: u8 = 0; let mut v___x_498_: u64 = 0; let mut v___x_499_: u8 = 0; let mut v___x_500_: *mut lean_object = core::ptr::null_mut(); let mut v___x_501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_508_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v_n_513_: *mut lean_object = core::ptr::null_mut(); let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); let mut v___x_516_: *mut lean_object = core::ptr::null_mut(); let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_520_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_521_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_522_: u8 = 0; let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_524_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_479_ = lean_ctor_get(v_a_476_, 0);
v_inner_480_ = lean_ctor_get(v_a_476_, 1);
v_isSharedCheck_524_ = (!lean_is_exclusive(v_a_476_)) as u8;
if v_isSharedCheck_524_ == 0 {
v___x_482_ = v_a_476_;
v_isShared_483_ = v_isSharedCheck_524_;
state = 1; continue;
} else {
lean_inc(v_inner_480_);
lean_inc(v_countdown_479_);
lean_dec(v_a_476_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_524_;
state = 1; continue;
}
}
1 => {
v___x_484_ = lean_unsigned_to_nat(1);
v___x_485_ = lean_nat_dec_eq(v_countdown_479_, v___x_484_);
if v___x_485_ == 0 {
let mut v_remaining_486_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_489_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_490_: u8 = 0; let mut v_isSharedCheck_522_: u8 = 0; 
v_remaining_486_ = lean_ctor_get(v_inner_480_, 0);
v_inner_487_ = lean_ctor_get(v_inner_480_, 1);
v_isSharedCheck_522_ = (!lean_is_exclusive(v_inner_480_)) as u8;
if v_isSharedCheck_522_ == 0 {
v___x_489_ = v_inner_480_;
v_isShared_490_ = v_isSharedCheck_522_;
state = 2; continue;
} else {
lean_inc(v_inner_487_);
lean_inc(v_remaining_486_);
lean_dec(v_inner_480_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_522_;
state = 2; continue;
}
} else {
let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_482_);
lean_dec(v_inner_480_);
lean_dec(v_countdown_479_);
v___x_523_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_523_, 0, v_b_477_);
return v___x_523_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg___boxed(mut v_map_525_: *mut lean_object, mut v_a_526_: *mut lean_object, mut v_b_527_: *mut lean_object, mut v___y_528_: *mut lean_object) -> *mut lean_object{
let mut v_res_529_: *mut lean_object = core::ptr::null_mut(); 
v_res_529_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg(v_map_525_, v_a_526_, v_b_527_);
lean_dec_ref(v_map_525_);
return v_res_529_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg(mut v_iter_530_: *mut lean_object, mut v_size_531_: *mut lean_object, mut v_map_532_: *mut lean_object, mut v_a_533_: *mut lean_object) -> *mut lean_object{
let mut v___x_535_: *mut lean_object = core::ptr::null_mut(); let mut v___x_536_: u8 = 0; let mut v___x_537_: *mut lean_object = core::ptr::null_mut(); let mut v___x_538_: *mut lean_object = core::ptr::null_mut(); let mut v___x_539_: *mut lean_object = core::ptr::null_mut(); let mut v___x_540_: *mut lean_object = core::ptr::null_mut(); let mut v___x_541_: *mut lean_object = core::ptr::null_mut(); let mut v___x_542_: *mut lean_object = core::ptr::null_mut(); let mut v_a_544_: *mut lean_object = core::ptr::null_mut(); let mut v___x_546_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_547_: u8 = 0; let mut v___x_549_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_550_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_551_: u8 = 0; let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_535_ = lean_unsigned_to_nat(0);
v___x_536_ = lean_nat_dec_eq(v_a_533_, v___x_535_);
if v___x_536_ == 0 {
let mut v___x_537_: *mut lean_object = core::ptr::null_mut(); let mut v___x_538_: *mut lean_object = core::ptr::null_mut(); let mut v___x_539_: *mut lean_object = core::ptr::null_mut(); let mut v___x_540_: *mut lean_object = core::ptr::null_mut(); let mut v___x_541_: *mut lean_object = core::ptr::null_mut(); 
v___x_537_ = lean_unsigned_to_nat(1);
v___x_538_ = lean_nat_add(v_size_531_, v___x_537_);
lean_inc_ref(v_iter_530_);
v___x_539_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_iter_530_);
v___x_540_ = lean_box(0);
v___x_541_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg(v_map_532_, v___x_539_, v___x_540_);
if lean_obj_tag(v___x_541_) == 0 {
let mut v___x_542_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_541_, 1);
v___x_542_ = lean_nat_sub(v_a_533_, v_size_531_);
lean_dec(v_a_533_);
v_a_533_ = v___x_542_;
state = 0; continue;
} else {
let mut v_a_544_: *mut lean_object = core::ptr::null_mut(); let mut v___x_546_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_547_: u8 = 0; let mut v_isSharedCheck_551_: u8 = 0; 
lean_dec(v_a_533_);
lean_dec_ref(v_iter_530_);
v_a_544_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_551_ = (!lean_is_exclusive(v___x_541_)) as u8;
if v_isSharedCheck_551_ == 0 {
v___x_546_ = v___x_541_;
v_isShared_547_ = v_isSharedCheck_551_;
state = 1; continue;
} else {
lean_inc(v_a_544_);
lean_dec(v___x_541_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
state = 1; continue;
}
}
} else {
let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_iter_530_);
v___x_552_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_552_, 0, v_a_533_);
return v___x_552_;
}
}
1 => {
if v_isShared_547_ == 0 {
v___x_549_ = v___x_546_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_550_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg___boxed(mut v_iter_553_: *mut lean_object, mut v_size_554_: *mut lean_object, mut v_map_555_: *mut lean_object, mut v_a_556_: *mut lean_object, mut v___y_557_: *mut lean_object) -> *mut lean_object{
let mut v_res_558_: *mut lean_object = core::ptr::null_mut(); 
v_res_558_ = l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg(v_iter_553_, v_size_554_, v_map_555_, v_a_556_);
lean_dec_ref(v_map_555_);
lean_dec(v_size_554_);
return v_res_558_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsMiss___lam__0(mut v_iter_559_: *mut lean_object, mut v_size_560_: *mut lean_object, mut v_map_561_: *mut lean_object, mut v_todo_562_: *mut lean_object) -> *mut lean_object{
let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_566_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_567_: u8 = 0; let mut v___x_568_: *mut lean_object = core::ptr::null_mut(); let mut v___x_570_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_571_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_572_: u8 = 0; let mut v_unused_573_: *mut lean_object = core::ptr::null_mut(); let mut v_a_574_: *mut lean_object = core::ptr::null_mut(); let mut v___x_576_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_577_: u8 = 0; let mut v___x_579_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_580_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_581_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_564_ = l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg(v_iter_559_, v_size_560_, v_map_561_, v_todo_562_);
if lean_obj_tag(v___x_564_) == 0 {
let mut v___x_566_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_567_: u8 = 0; let mut v_isSharedCheck_572_: u8 = 0; 
v_isSharedCheck_572_ = (!lean_is_exclusive(v___x_564_)) as u8;
if v_isSharedCheck_572_ == 0 {
let mut v_unused_573_: *mut lean_object = core::ptr::null_mut(); 
v_unused_573_ = lean_ctor_get(v___x_564_, 0);
lean_dec(v_unused_573_);
v___x_566_ = v___x_564_;
v_isShared_567_ = v_isSharedCheck_572_;
state = 1; continue;
} else {
lean_dec(v___x_564_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_572_;
state = 1; continue;
}
} else {
let mut v_a_574_: *mut lean_object = core::ptr::null_mut(); let mut v___x_576_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_577_: u8 = 0; let mut v_isSharedCheck_581_: u8 = 0; 
v_a_574_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_581_ = (!lean_is_exclusive(v___x_564_)) as u8;
if v_isSharedCheck_581_ == 0 {
v___x_576_ = v___x_564_;
v_isShared_577_ = v_isSharedCheck_581_;
state = 3; continue;
} else {
lean_inc(v_a_574_);
lean_dec(v___x_564_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
state = 3; continue;
}
}
}
1 => {
v___x_568_ = lean_box(0);
if v_isShared_567_ == 0 {
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_571_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
state = 2; continue;
}
}
3 => {
if v_isShared_577_ == 0 {
v___x_579_ = v___x_576_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_580_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsMiss___lam__0___boxed(mut v_iter_582_: *mut lean_object, mut v_size_583_: *mut lean_object, mut v_map_584_: *mut lean_object, mut v_todo_585_: *mut lean_object, mut v___y_586_: *mut lean_object) -> *mut lean_object{
let mut v_res_587_: *mut lean_object = core::ptr::null_mut(); 
v_res_587_ = l_benchContainsMiss___lam__0(v_iter_582_, v_size_583_, v_map_584_, v_todo_585_);
lean_dec_ref(v_map_584_);
lean_dec(v_size_583_);
return v_res_587_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsMiss(mut v_seed_588_: u64, mut v_size_589_: *mut lean_object) -> *mut lean_object{
let mut v_map_591_: *mut lean_object = core::ptr::null_mut(); let mut v___x_592_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_593_: *mut lean_object = core::ptr::null_mut(); let mut v___x_594_: *mut lean_object = core::ptr::null_mut(); let mut v_iter_595_: *mut lean_object = core::ptr::null_mut(); let mut v___f_596_: *mut lean_object = core::ptr::null_mut(); let mut v___x_597_: *mut lean_object = core::ptr::null_mut(); 
v_map_591_ = l_mkMapWithCap(v_seed_588_, v_size_589_);
v___x_592_ = lean_unsigned_to_nat(100);
v_todo_593_ = lean_nat_mul(v_size_589_, v___x_592_);
v___x_594_ = lean_box_uint64(v_seed_588_);
lean_inc(v_size_589_);
v_iter_595_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_iter_595_, 0, v_size_589_);
lean_ctor_set(v_iter_595_, 1, v___x_594_);
lean_inc(v_todo_593_);
v___f_596_ = lean_alloc_closure(l_benchContainsMiss___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
lean_closure_set(v___f_596_, 0, v_iter_595_);
lean_closure_set(v___f_596_, 1, v_size_589_);
lean_closure_set(v___f_596_, 2, v_map_591_);
lean_closure_set(v___f_596_, 3, v_todo_593_);
v___x_597_ = l_timeNanos(v_todo_593_, v___f_596_);
return v___x_597_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsMiss___boxed(mut v_seed_598_: *mut lean_object, mut v_size_599_: *mut lean_object, mut v_a_600_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_601_: u64 = 0; let mut v_res_602_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_601_ = lean_unbox_uint64(v_seed_598_);
lean_dec_ref(v_seed_598_);
v_res_602_ = l_benchContainsMiss(v_seed_boxed_601_, v_size_599_);
return v_res_602_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0(mut v_map_603_: *mut lean_object, mut v_inst_604_: *mut lean_object, mut v_R_605_: *mut lean_object, mut v_a_606_: *mut lean_object, mut v_b_607_: *mut lean_object, mut v_c_608_: *mut lean_object) -> *mut lean_object{
let mut v___x_610_: *mut lean_object = core::ptr::null_mut(); 
v___x_610_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg(v_map_603_, v_a_606_, v_b_607_);
return v___x_610_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___boxed(mut v_map_611_: *mut lean_object, mut v_inst_612_: *mut lean_object, mut v_R_613_: *mut lean_object, mut v_a_614_: *mut lean_object, mut v_b_615_: *mut lean_object, mut v_c_616_: *mut lean_object, mut v___y_617_: *mut lean_object) -> *mut lean_object{
let mut v_res_618_: *mut lean_object = core::ptr::null_mut(); 
v_res_618_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0(v_map_611_, v_inst_612_, v_R_613_, v_a_614_, v_b_615_, v_c_616_);
lean_dec_ref(v_map_611_);
return v_res_618_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1(mut v_iter_619_: *mut lean_object, mut v_size_620_: *mut lean_object, mut v_map_621_: *mut lean_object, mut v_inst_622_: *mut lean_object, mut v_a_623_: *mut lean_object) -> *mut lean_object{
let mut v___x_625_: *mut lean_object = core::ptr::null_mut(); 
v___x_625_ = l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg(v_iter_619_, v_size_620_, v_map_621_, v_a_623_);
return v___x_625_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___boxed(mut v_iter_626_: *mut lean_object, mut v_size_627_: *mut lean_object, mut v_map_628_: *mut lean_object, mut v_inst_629_: *mut lean_object, mut v_a_630_: *mut lean_object, mut v___y_631_: *mut lean_object) -> *mut lean_object{
let mut v_res_632_: *mut lean_object = core::ptr::null_mut(); 
v_res_632_ = l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1(v_iter_626_, v_size_627_, v_map_628_, v_inst_629_, v_a_630_);
lean_dec_ref(v_map_628_);
lean_dec(v_size_627_);
return v_res_632_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00benchIterate_spec__0(mut v_a_633_: *mut lean_object, mut v_a_634_: u64) -> *mut lean_object{
let mut v___x_636_: *mut lean_object = core::ptr::null_mut(); let mut v___x_637_: *mut lean_object = core::ptr::null_mut(); let mut v___x_638_: *mut lean_object = core::ptr::null_mut(); let mut v_key_639_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_640_: *mut lean_object = core::ptr::null_mut(); let mut v_sum_641_: u64 = 0; let mut v___x_642_: u64 = 0; let mut v___x_643_: u64 = 0; let mut v___x_644_: u8 = 0; let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v___x_647_: *mut lean_object = core::ptr::null_mut(); let mut v___x_648_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_a_633_) == 0 {
let mut v___x_636_: *mut lean_object = core::ptr::null_mut(); let mut v___x_637_: *mut lean_object = core::ptr::null_mut(); let mut v___x_638_: *mut lean_object = core::ptr::null_mut(); 
v___x_636_ = lean_box_uint64(v_a_634_);
v___x_637_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_637_, 0, v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
} else {
let mut v_key_639_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_640_: *mut lean_object = core::ptr::null_mut(); let mut v_sum_641_: u64 = 0; let mut v___x_642_: u64 = 0; let mut v___x_643_: u64 = 0; let mut v___x_644_: u8 = 0; 
v_key_639_ = lean_ctor_get(v_a_633_, 0);
v_tail_640_ = lean_ctor_get(v_a_633_, 2);
v_sum_641_ = 0u64;
v___x_642_ = lean_unbox_uint64(v_key_639_);
v___x_643_ = lean_uint64_add(v_a_634_, v___x_642_);
v___x_644_ = lean_uint64_dec_eq(v___x_643_, v_sum_641_);
if v___x_644_ == 0 {
v_a_633_ = v_tail_640_;
v_a_634_ = v___x_643_;
state = 0; continue;
} else {
let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v___x_647_: *mut lean_object = core::ptr::null_mut(); let mut v___x_648_: *mut lean_object = core::ptr::null_mut(); 
v___x_646_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_647_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___x_648_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00benchIterate_spec__0___boxed(mut v_a_649_: *mut lean_object, mut v_a_650_: *mut lean_object, mut v___y_651_: *mut lean_object) -> *mut lean_object{
let mut v_a_1238__boxed_652_: u64 = 0; let mut v_res_653_: *mut lean_object = core::ptr::null_mut(); 
v_a_1238__boxed_652_ = lean_unbox_uint64(v_a_650_);
lean_dec_ref(v_a_650_);
v_res_653_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00benchIterate_spec__0(v_a_649_, v_a_1238__boxed_652_);
lean_dec(v_a_649_);
return v_res_653_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00benchIterate_spec__1(mut v_as_654_: *mut lean_object, mut v_sz_655_: usize, mut v_i_656_: usize, mut v_b_657_: u64) -> *mut lean_object{
let mut v___x_659_: u8 = 0; let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); let mut v___x_661_: *mut lean_object = core::ptr::null_mut(); let mut v_a_662_: *mut lean_object = core::ptr::null_mut(); let mut v___x_663_: *mut lean_object = core::ptr::null_mut(); let mut v_a_664_: *mut lean_object = core::ptr::null_mut(); let mut v___x_666_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_667_: u8 = 0; let mut v_a_668_: *mut lean_object = core::ptr::null_mut(); let mut v___x_670_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_671_: *mut lean_object = core::ptr::null_mut(); let mut v_a_672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_673_: usize = 0; let mut v___x_674_: usize = 0; let mut v___x_675_: u64 = 0; let mut v_isSharedCheck_677_: u8 = 0; let mut v_a_678_: *mut lean_object = core::ptr::null_mut(); let mut v___x_680_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_681_: u8 = 0; let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_684_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_685_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_659_ = lean_usize_dec_lt(v_i_656_, v_sz_655_);
if v___x_659_ == 0 {
let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); let mut v___x_661_: *mut lean_object = core::ptr::null_mut(); 
v___x_660_ = lean_box_uint64(v_b_657_);
v___x_661_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
} else {
let mut v_a_662_: *mut lean_object = core::ptr::null_mut(); let mut v___x_663_: *mut lean_object = core::ptr::null_mut(); 
v_a_662_ = lean_array_uget_borrowed(v_as_654_, v_i_656_);
v___x_663_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00benchIterate_spec__0(v_a_662_, v_b_657_);
if lean_obj_tag(v___x_663_) == 0 {
let mut v_a_664_: *mut lean_object = core::ptr::null_mut(); let mut v___x_666_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_667_: u8 = 0; let mut v_isSharedCheck_677_: u8 = 0; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_677_ = (!lean_is_exclusive(v___x_663_)) as u8;
if v_isSharedCheck_677_ == 0 {
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_677_;
state = 1; continue;
} else {
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_677_;
state = 1; continue;
}
} else {
let mut v_a_678_: *mut lean_object = core::ptr::null_mut(); let mut v___x_680_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_681_: u8 = 0; let mut v_isSharedCheck_685_: u8 = 0; 
v_a_678_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_685_ = (!lean_is_exclusive(v___x_663_)) as u8;
if v_isSharedCheck_685_ == 0 {
v___x_680_ = v___x_663_;
v_isShared_681_ = v_isSharedCheck_685_;
state = 3; continue;
} else {
lean_inc(v_a_678_);
lean_dec(v___x_663_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
state = 3; continue;
}
}
}
}
1 => {
if lean_obj_tag(v_a_664_) == 0 {
let mut v_a_668_: *mut lean_object = core::ptr::null_mut(); let mut v___x_670_: *mut lean_object = core::ptr::null_mut(); 
v_a_668_ = lean_ctor_get(v_a_664_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v_a_664_, 1);
if v_isShared_667_ == 0 {
lean_ctor_set(v___x_666_, 0, v_a_668_);
v___x_670_ = v___x_666_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_671_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_668_);
v___x_670_ = v_reuseFailAlloc_671_;
state = 2; continue;
}
} else {
let mut v_a_672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_673_: usize = 0; let mut v___x_674_: usize = 0; let mut v___x_675_: u64 = 0; 
lean_del_object(v___x_666_);
v_a_672_ = lean_ctor_get(v_a_664_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v_a_664_, 1);
v___x_673_ = 1usize;
v___x_674_ = lean_usize_add(v_i_656_, v___x_673_);
v___x_675_ = lean_unbox_uint64(v_a_672_);
lean_dec(v_a_672_);
v_i_656_ = v___x_674_;
v_b_657_ = v___x_675_;
state = 0; continue;
}
}
3 => {
if v_isShared_681_ == 0 {
v___x_683_ = v___x_680_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_684_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00benchIterate_spec__1___boxed(mut v_as_686_: *mut lean_object, mut v_sz_687_: *mut lean_object, mut v_i_688_: *mut lean_object, mut v_b_689_: *mut lean_object, mut v___y_690_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_691_: usize = 0; let mut v_i_boxed_692_: usize = 0; let mut v_b_boxed_693_: u64 = 0; let mut v_res_694_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_691_ = lean_unbox_usize(v_sz_687_);
lean_dec(v_sz_687_);
v_i_boxed_692_ = lean_unbox_usize(v_i_688_);
lean_dec(v_i_688_);
v_b_boxed_693_ = lean_unbox_uint64(v_b_689_);
lean_dec_ref(v_b_689_);
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00benchIterate_spec__1(v_as_686_, v_sz_boxed_691_, v_i_boxed_692_, v_b_boxed_693_);
lean_dec_ref(v_as_686_);
return v_res_694_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__2___redArg(mut v_map_695_: *mut lean_object, mut v_size_696_: *mut lean_object, mut v_a_697_: *mut lean_object) -> *mut lean_object{
let mut v_fst_699_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_700_: *mut lean_object = core::ptr::null_mut(); let mut v___x_702_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_703_: u8 = 0; let mut v___x_704_: *mut lean_object = core::ptr::null_mut(); let mut v___x_705_: u8 = 0; let mut v_buckets_706_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_707_: usize = 0; let mut v___x_708_: usize = 0; let mut v___x_709_: u64 = 0; let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); let mut v_a_711_: *mut lean_object = core::ptr::null_mut(); let mut v___x_712_: *mut lean_object = core::ptr::null_mut(); let mut v___x_714_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_716_: *mut lean_object = core::ptr::null_mut(); let mut v_a_717_: *mut lean_object = core::ptr::null_mut(); let mut v___x_719_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_720_: u8 = 0; let mut v___x_722_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_723_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_724_: u8 = 0; let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_727_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_728_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_729_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_699_ = lean_ctor_get(v_a_697_, 0);
v_snd_700_ = lean_ctor_get(v_a_697_, 1);
v_isSharedCheck_729_ = (!lean_is_exclusive(v_a_697_)) as u8;
if v_isSharedCheck_729_ == 0 {
v___x_702_ = v_a_697_;
v_isShared_703_ = v_isSharedCheck_729_;
state = 1; continue;
} else {
lean_inc(v_snd_700_);
lean_inc(v_fst_699_);
lean_dec(v_a_697_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_729_;
state = 1; continue;
}
}
1 => {
v___x_704_ = lean_unsigned_to_nat(0);
v___x_705_ = lean_nat_dec_eq(v_fst_699_, v___x_704_);
if v___x_705_ == 0 {
let mut v_buckets_706_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_707_: usize = 0; let mut v___x_708_: usize = 0; let mut v___x_709_: u64 = 0; let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); 
v_buckets_706_ = lean_ctor_get(v_map_695_, 1);
v_sz_707_ = lean_array_size(v_buckets_706_);
v___x_708_ = 0usize;
v___x_709_ = lean_unbox_uint64(v_snd_700_);
lean_dec(v_snd_700_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00benchIterate_spec__1(v_buckets_706_, v_sz_707_, v___x_708_, v___x_709_);
if lean_obj_tag(v___x_710_) == 0 {
let mut v_a_711_: *mut lean_object = core::ptr::null_mut(); let mut v___x_712_: *mut lean_object = core::ptr::null_mut(); let mut v___x_714_: *mut lean_object = core::ptr::null_mut(); 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_nat_sub(v_fst_699_, v_size_696_);
lean_dec(v_fst_699_);
if v_isShared_703_ == 0 {
lean_ctor_set(v___x_702_, 1, v_a_711_);
lean_ctor_set(v___x_702_, 0, v___x_712_);
v___x_714_ = v___x_702_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_716_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_a_711_);
v___x_714_ = v_reuseFailAlloc_716_;
state = 2; continue;
}
} else {
let mut v_a_717_: *mut lean_object = core::ptr::null_mut(); let mut v___x_719_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_720_: u8 = 0; let mut v_isSharedCheck_724_: u8 = 0; 
lean_del_object(v___x_702_);
lean_dec(v_fst_699_);
v_a_717_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_724_ = (!lean_is_exclusive(v___x_710_)) as u8;
if v_isSharedCheck_724_ == 0 {
v___x_719_ = v___x_710_;
v_isShared_720_ = v_isSharedCheck_724_;
state = 3; continue;
} else {
lean_inc(v_a_717_);
lean_dec(v___x_710_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
state = 3; continue;
}
}
} else {
let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_703_ == 0 {
v___x_726_ = v___x_702_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_728_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_fst_699_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_snd_700_);
v___x_726_ = v_reuseFailAlloc_728_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__2___redArg___boxed(mut v_map_730_: *mut lean_object, mut v_size_731_: *mut lean_object, mut v_a_732_: *mut lean_object, mut v___y_733_: *mut lean_object) -> *mut lean_object{
let mut v_res_734_: *mut lean_object = core::ptr::null_mut(); 
v_res_734_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__2___redArg(v_map_730_, v_size_731_, v_a_732_);
lean_dec(v_size_731_);
lean_dec_ref(v_map_730_);
return v_res_734_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterate___lam__0(mut v_map_735_: *mut lean_object, mut v_size_736_: *mut lean_object, mut v___x_737_: *mut lean_object) -> *mut lean_object{
let mut v___x_739_: *mut lean_object = core::ptr::null_mut(); let mut v___x_741_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_742_: u8 = 0; let mut v___x_743_: *mut lean_object = core::ptr::null_mut(); let mut v___x_745_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_746_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_747_: u8 = 0; let mut v_unused_748_: *mut lean_object = core::ptr::null_mut(); let mut v_a_749_: *mut lean_object = core::ptr::null_mut(); let mut v___x_751_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_752_: u8 = 0; let mut v___x_754_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_755_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_756_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_739_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__2___redArg(v_map_735_, v_size_736_, v___x_737_);
if lean_obj_tag(v___x_739_) == 0 {
let mut v___x_741_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_742_: u8 = 0; let mut v_isSharedCheck_747_: u8 = 0; 
v_isSharedCheck_747_ = (!lean_is_exclusive(v___x_739_)) as u8;
if v_isSharedCheck_747_ == 0 {
let mut v_unused_748_: *mut lean_object = core::ptr::null_mut(); 
v_unused_748_ = lean_ctor_get(v___x_739_, 0);
lean_dec(v_unused_748_);
v___x_741_ = v___x_739_;
v_isShared_742_ = v_isSharedCheck_747_;
state = 1; continue;
} else {
lean_dec(v___x_739_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
state = 1; continue;
}
} else {
let mut v_a_749_: *mut lean_object = core::ptr::null_mut(); let mut v___x_751_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_752_: u8 = 0; let mut v_isSharedCheck_756_: u8 = 0; 
v_a_749_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_756_ = (!lean_is_exclusive(v___x_739_)) as u8;
if v_isSharedCheck_756_ == 0 {
v___x_751_ = v___x_739_;
v_isShared_752_ = v_isSharedCheck_756_;
state = 3; continue;
} else {
lean_inc(v_a_749_);
lean_dec(v___x_739_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
state = 3; continue;
}
}
}
1 => {
v___x_743_ = lean_box(0);
if v_isShared_742_ == 0 {
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_745_ = v___x_741_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_746_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
state = 2; continue;
}
}
3 => {
if v_isShared_752_ == 0 {
v___x_754_ = v___x_751_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_755_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterate___lam__0___boxed(mut v_map_757_: *mut lean_object, mut v_size_758_: *mut lean_object, mut v___x_759_: *mut lean_object, mut v___y_760_: *mut lean_object) -> *mut lean_object{
let mut v_res_761_: *mut lean_object = core::ptr::null_mut(); 
v_res_761_ = l_benchIterate___lam__0(v_map_757_, v_size_758_, v___x_759_);
lean_dec(v_size_758_);
lean_dec_ref(v_map_757_);
return v_res_761_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterate(mut v_seed_764_: u64, mut v_size_765_: *mut lean_object) -> *mut lean_object{
let mut v_map_767_: *mut lean_object = core::ptr::null_mut(); let mut v___x_768_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_769_: *mut lean_object = core::ptr::null_mut(); let mut v___x_770_: *mut lean_object = core::ptr::null_mut(); let mut v___x_771_: *mut lean_object = core::ptr::null_mut(); let mut v___f_772_: *mut lean_object = core::ptr::null_mut(); let mut v___x_773_: *mut lean_object = core::ptr::null_mut(); 
v_map_767_ = l_mkMapWithCap(v_seed_764_, v_size_765_);
v___x_768_ = lean_unsigned_to_nat(100);
v_todo_769_ = lean_nat_mul(v_size_765_, v___x_768_);
v___x_770_ = l_benchIterate___boxed__const__1;
lean_inc(v_todo_769_);
v___x_771_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_771_, 0, v_todo_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___f_772_ = lean_alloc_closure(l_benchIterate___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_772_, 0, v_map_767_);
lean_closure_set(v___f_772_, 1, v_size_765_);
lean_closure_set(v___f_772_, 2, v___x_771_);
v___x_773_ = l_timeNanos(v_todo_769_, v___f_772_);
return v___x_773_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterate___boxed(mut v_seed_774_: *mut lean_object, mut v_size_775_: *mut lean_object, mut v_a_776_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_777_: u64 = 0; let mut v_res_778_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_777_ = lean_unbox_uint64(v_seed_774_);
lean_dec_ref(v_seed_774_);
v_res_778_ = l_benchIterate(v_seed_boxed_777_, v_size_775_);
return v_res_778_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__2(mut v_map_779_: *mut lean_object, mut v_size_780_: *mut lean_object, mut v_inst_781_: *mut lean_object, mut v_a_782_: *mut lean_object) -> *mut lean_object{
let mut v___x_784_: *mut lean_object = core::ptr::null_mut(); 
v___x_784_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__2___redArg(v_map_779_, v_size_780_, v_a_782_);
return v___x_784_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__2___boxed(mut v_map_785_: *mut lean_object, mut v_size_786_: *mut lean_object, mut v_inst_787_: *mut lean_object, mut v_a_788_: *mut lean_object, mut v___y_789_: *mut lean_object) -> *mut lean_object{
let mut v_res_790_: *mut lean_object = core::ptr::null_mut(); 
v_res_790_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__2(v_map_785_, v_size_786_, v_inst_787_, v_a_788_);
lean_dec(v_size_786_);
lean_dec_ref(v_map_785_);
return v_res_790_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00benchInsertIfNewHit_spec__0___redArg(mut v_m_791_: *mut lean_object, mut v_a_792_: u64, mut v_b_793_: *mut lean_object) -> *mut lean_object{
let mut v_size_794_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_795_: *mut lean_object = core::ptr::null_mut(); let mut v___x_796_: *mut lean_object = core::ptr::null_mut(); let mut v___x_797_: u64 = 0; let mut v___x_798_: u64 = 0; let mut v_fold_799_: u64 = 0; let mut v___x_800_: u64 = 0; let mut v___x_801_: u64 = 0; let mut v___x_802_: u64 = 0; let mut v___x_803_: usize = 0; let mut v___x_804_: usize = 0; let mut v___x_805_: usize = 0; let mut v___x_806_: usize = 0; let mut v___x_807_: usize = 0; let mut v_bkt_808_: *mut lean_object = core::ptr::null_mut(); let mut v___x_809_: u8 = 0; let mut v___x_811_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_812_: u8 = 0; let mut v___x_813_: *mut lean_object = core::ptr::null_mut(); let mut v_size_x27_814_: *mut lean_object = core::ptr::null_mut(); let mut v___x_815_: *mut lean_object = core::ptr::null_mut(); let mut v___x_816_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_x27_817_: *mut lean_object = core::ptr::null_mut(); let mut v___x_818_: *mut lean_object = core::ptr::null_mut(); let mut v___x_819_: *mut lean_object = core::ptr::null_mut(); let mut v___x_820_: *mut lean_object = core::ptr::null_mut(); let mut v___x_821_: *mut lean_object = core::ptr::null_mut(); let mut v___x_822_: *mut lean_object = core::ptr::null_mut(); let mut v___x_823_: u8 = 0; let mut v_val_824_: *mut lean_object = core::ptr::null_mut(); let mut v___x_826_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_827_: *mut lean_object = core::ptr::null_mut(); let mut v___x_829_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_830_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_831_: u8 = 0; let mut v_unused_832_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_833_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_size_794_ = lean_ctor_get(v_m_791_, 0);
v_buckets_795_ = lean_ctor_get(v_m_791_, 1);
v___x_796_ = lean_array_get_size(v_buckets_795_);
v___x_797_ = 32u64;
v___x_798_ = lean_uint64_shift_right(v_a_792_, v___x_797_);
v_fold_799_ = lean_uint64_xor(v_a_792_, v___x_798_);
v___x_800_ = 16u64;
v___x_801_ = lean_uint64_shift_right(v_fold_799_, v___x_800_);
v___x_802_ = lean_uint64_xor(v_fold_799_, v___x_801_);
v___x_803_ = lean_uint64_to_usize(v___x_802_);
v___x_804_ = lean_usize_of_nat(v___x_796_);
v___x_805_ = 1usize;
v___x_806_ = lean_usize_sub(v___x_804_, v___x_805_);
v___x_807_ = lean_usize_land(v___x_803_, v___x_806_);
v_bkt_808_ = lean_array_uget_borrowed(v_buckets_795_, v___x_807_);
v___x_809_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_a_792_, v_bkt_808_);
if v___x_809_ == 0 {
let mut v___x_811_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_812_: u8 = 0; let mut v_isSharedCheck_831_: u8 = 0; 
lean_inc_ref(v_buckets_795_);
lean_inc(v_size_794_);
v_isSharedCheck_831_ = (!lean_is_exclusive(v_m_791_)) as u8;
if v_isSharedCheck_831_ == 0 {
let mut v_unused_832_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_833_: *mut lean_object = core::ptr::null_mut(); 
v_unused_832_ = lean_ctor_get(v_m_791_, 1);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_m_791_, 0);
lean_dec(v_unused_833_);
v___x_811_ = v_m_791_;
v_isShared_812_ = v_isSharedCheck_831_;
state = 1; continue;
} else {
lean_dec(v_m_791_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_831_;
state = 1; continue;
}
} else {
lean_dec(v_b_793_);
return v_m_791_;
}
}
1 => {
v___x_813_ = lean_unsigned_to_nat(1);
v_size_x27_814_ = lean_nat_add(v_size_794_, v___x_813_);
lean_dec(v_size_794_);
v___x_815_ = lean_box_uint64(v_a_792_);
lean_inc(v_bkt_808_);
v___x_816_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v_b_793_);
lean_ctor_set(v___x_816_, 2, v_bkt_808_);
v_buckets_x27_817_ = lean_array_uset(v_buckets_795_, v___x_807_, v___x_816_);
v___x_818_ = lean_unsigned_to_nat(4);
v___x_819_ = lean_nat_mul(v_size_x27_814_, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(3);
v___x_821_ = lean_nat_div(v___x_819_, v___x_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_array_get_size(v_buckets_x27_817_);
v___x_823_ = lean_nat_dec_le(v___x_821_, v___x_822_);
lean_dec(v___x_821_);
if v___x_823_ == 0 {
let mut v_val_824_: *mut lean_object = core::ptr::null_mut(); let mut v___x_826_: *mut lean_object = core::ptr::null_mut(); 
v_val_824_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__1___redArg(v_buckets_x27_817_);
if v_isShared_812_ == 0 {
lean_ctor_set(v___x_811_, 1, v_val_824_);
lean_ctor_set(v___x_811_, 0, v_size_x27_814_);
v___x_826_ = v___x_811_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_827_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_size_x27_814_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
state = 2; continue;
}
} else {
let mut v___x_829_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_812_ == 0 {
lean_ctor_set(v___x_811_, 1, v_buckets_x27_817_);
lean_ctor_set(v___x_811_, 0, v_size_x27_814_);
v___x_829_ = v___x_811_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_830_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_size_x27_814_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_buckets_x27_817_);
v___x_829_ = v_reuseFailAlloc_830_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00benchInsertIfNewHit_spec__0___redArg___boxed(mut v_m_834_: *mut lean_object, mut v_a_835_: *mut lean_object, mut v_b_836_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_837_: u64 = 0; let mut v_res_838_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_837_ = lean_unbox_uint64(v_a_835_);
lean_dec_ref(v_a_835_);
v_res_838_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00benchInsertIfNewHit_spec__0___redArg(v_m_834_, v_a_boxed_837_, v_b_836_);
return v_res_838_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1___redArg(mut v_size_839_: *mut lean_object, mut v_a_840_: *mut lean_object, mut v_b_841_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_843_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_844_: *mut lean_object = core::ptr::null_mut(); let mut v___x_846_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_847_: u8 = 0; let mut v___x_848_: *mut lean_object = core::ptr::null_mut(); let mut v___x_849_: u8 = 0; let mut v___x_850_: u64 = 0; let mut v___x_851_: u64 = 0; let mut v___x_852_: u64 = 0; let mut v___x_853_: u64 = 0; let mut v___x_854_: *mut lean_object = core::ptr::null_mut(); let mut v_size_855_: *mut lean_object = core::ptr::null_mut(); let mut v___x_856_: u8 = 0; let mut v___x_857_: *mut lean_object = core::ptr::null_mut(); let mut v___x_858_: *mut lean_object = core::ptr::null_mut(); let mut v___x_859_: *mut lean_object = core::ptr::null_mut(); let mut v___x_860_: u64 = 0; let mut v___x_861_: u64 = 0; let mut v___x_862_: *mut lean_object = core::ptr::null_mut(); let mut v___x_863_: *mut lean_object = core::ptr::null_mut(); let mut v___x_865_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_867_: *mut lean_object = core::ptr::null_mut(); let mut v___x_868_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_869_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_843_ = lean_ctor_get(v_a_840_, 0);
v_inner_844_ = lean_ctor_get(v_a_840_, 1);
v_isSharedCheck_869_ = (!lean_is_exclusive(v_a_840_)) as u8;
if v_isSharedCheck_869_ == 0 {
v___x_846_ = v_a_840_;
v_isShared_847_ = v_isSharedCheck_869_;
state = 1; continue;
} else {
lean_inc(v_inner_844_);
lean_inc(v_countdown_843_);
lean_dec(v_a_840_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_869_;
state = 1; continue;
}
}
1 => {
v___x_848_ = lean_unsigned_to_nat(1);
v___x_849_ = lean_nat_dec_eq(v_countdown_843_, v___x_848_);
if v___x_849_ == 0 {
let mut v___x_850_: u64 = 0; let mut v___x_851_: u64 = 0; let mut v___x_852_: u64 = 0; let mut v___x_853_: u64 = 0; let mut v___x_854_: *mut lean_object = core::ptr::null_mut(); let mut v_size_855_: *mut lean_object = core::ptr::null_mut(); let mut v___x_856_: u8 = 0; 
v___x_850_ = 1u64;
v___x_851_ = lean_unbox_uint64(v_inner_844_);
v___x_852_ = lean_uint64_add(v___x_851_, v___x_850_);
v___x_853_ = lean_unbox_uint64(v_inner_844_);
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00benchInsertIfNewHit_spec__0___redArg(v_b_841_, v___x_853_, v_inner_844_);
v_size_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_size_855_);
v___x_856_ = lean_nat_dec_eq(v_size_855_, v_size_839_);
lean_dec(v_size_855_);
if v___x_856_ == 0 {
let mut v___x_857_: *mut lean_object = core::ptr::null_mut(); let mut v___x_858_: *mut lean_object = core::ptr::null_mut(); let mut v___x_859_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v___x_854_);
lean_del_object(v___x_846_);
lean_dec(v_countdown_843_);
v___x_857_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_858_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_858_, 0, v___x_857_);
v___x_859_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
} else {
let mut v___x_860_: u64 = 0; let mut v___x_861_: u64 = 0; let mut v___x_862_: *mut lean_object = core::ptr::null_mut(); let mut v___x_863_: *mut lean_object = core::ptr::null_mut(); let mut v___x_865_: *mut lean_object = core::ptr::null_mut(); 
v___x_860_ = 3787392781u64;
v___x_861_ = lean_uint64_mul(v___x_852_, v___x_860_);
v___x_862_ = lean_nat_sub(v_countdown_843_, v___x_848_);
lean_dec(v_countdown_843_);
v___x_863_ = lean_box_uint64(v___x_861_);
if v_isShared_847_ == 0 {
lean_ctor_set(v___x_846_, 1, v___x_863_);
lean_ctor_set(v___x_846_, 0, v___x_862_);
v___x_865_ = v___x_846_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_867_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_867_;
state = 2; continue;
}
}
} else {
let mut v___x_868_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_846_);
lean_dec(v_inner_844_);
lean_dec(v_countdown_843_);
v___x_868_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_868_, 0, v_b_841_);
return v___x_868_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1___redArg___boxed(mut v_size_870_: *mut lean_object, mut v_a_871_: *mut lean_object, mut v_b_872_: *mut lean_object, mut v___y_873_: *mut lean_object) -> *mut lean_object{
let mut v_res_874_: *mut lean_object = core::ptr::null_mut(); 
v_res_874_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1___redArg(v_size_870_, v_a_871_, v_b_872_);
lean_dec(v_size_870_);
return v_res_874_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2_spec__2___redArg(mut v_seed_875_: u64, mut v_size_876_: *mut lean_object, mut v_a_877_: *mut lean_object) -> *mut lean_object{
let mut v_fst_879_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_880_: *mut lean_object = core::ptr::null_mut(); let mut v___x_882_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_883_: u8 = 0; let mut v___x_884_: *mut lean_object = core::ptr::null_mut(); let mut v___x_885_: u8 = 0; let mut v___x_886_: *mut lean_object = core::ptr::null_mut(); let mut v___x_887_: *mut lean_object = core::ptr::null_mut(); let mut v___x_888_: *mut lean_object = core::ptr::null_mut(); let mut v___x_889_: *mut lean_object = core::ptr::null_mut(); let mut v___x_890_: *mut lean_object = core::ptr::null_mut(); let mut v_a_891_: *mut lean_object = core::ptr::null_mut(); let mut v___x_892_: *mut lean_object = core::ptr::null_mut(); let mut v___x_894_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_896_: *mut lean_object = core::ptr::null_mut(); let mut v_a_897_: *mut lean_object = core::ptr::null_mut(); let mut v___x_899_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_900_: u8 = 0; let mut v___x_902_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_903_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_904_: u8 = 0; let mut v___x_906_: *mut lean_object = core::ptr::null_mut(); let mut v___x_907_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_908_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_909_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_879_ = lean_ctor_get(v_a_877_, 0);
v_snd_880_ = lean_ctor_get(v_a_877_, 1);
v_isSharedCheck_909_ = (!lean_is_exclusive(v_a_877_)) as u8;
if v_isSharedCheck_909_ == 0 {
v___x_882_ = v_a_877_;
v_isShared_883_ = v_isSharedCheck_909_;
state = 1; continue;
} else {
lean_inc(v_snd_880_);
lean_inc(v_fst_879_);
lean_dec(v_a_877_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_909_;
state = 1; continue;
}
}
1 => {
v___x_884_ = lean_unsigned_to_nat(0);
v___x_885_ = lean_nat_dec_eq(v_fst_879_, v___x_884_);
if v___x_885_ == 0 {
let mut v___x_886_: *mut lean_object = core::ptr::null_mut(); let mut v___x_887_: *mut lean_object = core::ptr::null_mut(); let mut v___x_888_: *mut lean_object = core::ptr::null_mut(); let mut v___x_889_: *mut lean_object = core::ptr::null_mut(); let mut v___x_890_: *mut lean_object = core::ptr::null_mut(); 
v___x_886_ = lean_unsigned_to_nat(1);
v___x_887_ = lean_nat_add(v_size_876_, v___x_886_);
v___x_888_ = lean_box_uint64(v_seed_875_);
v___x_889_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1___redArg(v_size_876_, v___x_889_, v_snd_880_);
if lean_obj_tag(v___x_890_) == 0 {
let mut v_a_891_: *mut lean_object = core::ptr::null_mut(); let mut v___x_892_: *mut lean_object = core::ptr::null_mut(); let mut v___x_894_: *mut lean_object = core::ptr::null_mut(); 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = lean_nat_sub(v_fst_879_, v_size_876_);
lean_dec(v_fst_879_);
if v_isShared_883_ == 0 {
lean_ctor_set(v___x_882_, 1, v_a_891_);
lean_ctor_set(v___x_882_, 0, v___x_892_);
v___x_894_ = v___x_882_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_896_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_a_891_);
v___x_894_ = v_reuseFailAlloc_896_;
state = 2; continue;
}
} else {
let mut v_a_897_: *mut lean_object = core::ptr::null_mut(); let mut v___x_899_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_900_: u8 = 0; let mut v_isSharedCheck_904_: u8 = 0; 
lean_del_object(v___x_882_);
lean_dec(v_fst_879_);
v_a_897_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_904_ = (!lean_is_exclusive(v___x_890_)) as u8;
if v_isSharedCheck_904_ == 0 {
v___x_899_ = v___x_890_;
v_isShared_900_ = v_isSharedCheck_904_;
state = 3; continue;
} else {
lean_inc(v_a_897_);
lean_dec(v___x_890_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
state = 3; continue;
}
}
} else {
let mut v___x_906_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_883_ == 0 {
v___x_906_ = v___x_882_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_908_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_fst_879_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_snd_880_);
v___x_906_ = v_reuseFailAlloc_908_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2_spec__2___redArg___boxed(mut v_seed_910_: *mut lean_object, mut v_size_911_: *mut lean_object, mut v_a_912_: *mut lean_object, mut v___y_913_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_914_: u64 = 0; let mut v_res_915_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_914_ = lean_unbox_uint64(v_seed_910_);
lean_dec_ref(v_seed_910_);
v_res_915_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2_spec__2___redArg(v_seed_boxed_914_, v_size_911_, v_a_912_);
lean_dec(v_size_911_);
return v_res_915_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2___redArg(mut v_size_916_: *mut lean_object, mut v_seed_917_: u64, mut v_a_918_: *mut lean_object) -> *mut lean_object{
let mut v_fst_920_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_921_: *mut lean_object = core::ptr::null_mut(); let mut v___x_923_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_924_: u8 = 0; let mut v___x_925_: *mut lean_object = core::ptr::null_mut(); let mut v___x_926_: u8 = 0; let mut v___x_927_: *mut lean_object = core::ptr::null_mut(); let mut v___x_928_: *mut lean_object = core::ptr::null_mut(); let mut v___x_929_: *mut lean_object = core::ptr::null_mut(); let mut v___x_930_: *mut lean_object = core::ptr::null_mut(); let mut v___x_931_: *mut lean_object = core::ptr::null_mut(); let mut v_a_932_: *mut lean_object = core::ptr::null_mut(); let mut v___x_933_: *mut lean_object = core::ptr::null_mut(); let mut v___x_935_: *mut lean_object = core::ptr::null_mut(); let mut v___x_936_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_937_: *mut lean_object = core::ptr::null_mut(); let mut v_a_938_: *mut lean_object = core::ptr::null_mut(); let mut v___x_940_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_941_: u8 = 0; let mut v___x_943_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_944_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_945_: u8 = 0; let mut v___x_947_: *mut lean_object = core::ptr::null_mut(); let mut v___x_948_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_949_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_950_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_920_ = lean_ctor_get(v_a_918_, 0);
v_snd_921_ = lean_ctor_get(v_a_918_, 1);
v_isSharedCheck_950_ = (!lean_is_exclusive(v_a_918_)) as u8;
if v_isSharedCheck_950_ == 0 {
v___x_923_ = v_a_918_;
v_isShared_924_ = v_isSharedCheck_950_;
state = 1; continue;
} else {
lean_inc(v_snd_921_);
lean_inc(v_fst_920_);
lean_dec(v_a_918_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_950_;
state = 1; continue;
}
}
1 => {
v___x_925_ = lean_unsigned_to_nat(0);
v___x_926_ = lean_nat_dec_eq(v_fst_920_, v___x_925_);
if v___x_926_ == 0 {
let mut v___x_927_: *mut lean_object = core::ptr::null_mut(); let mut v___x_928_: *mut lean_object = core::ptr::null_mut(); let mut v___x_929_: *mut lean_object = core::ptr::null_mut(); let mut v___x_930_: *mut lean_object = core::ptr::null_mut(); let mut v___x_931_: *mut lean_object = core::ptr::null_mut(); 
v___x_927_ = lean_unsigned_to_nat(1);
v___x_928_ = lean_nat_add(v_size_916_, v___x_927_);
v___x_929_ = lean_box_uint64(v_seed_917_);
v___x_930_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1___redArg(v_size_916_, v___x_930_, v_snd_921_);
if lean_obj_tag(v___x_931_) == 0 {
let mut v_a_932_: *mut lean_object = core::ptr::null_mut(); let mut v___x_933_: *mut lean_object = core::ptr::null_mut(); let mut v___x_935_: *mut lean_object = core::ptr::null_mut(); 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = lean_nat_sub(v_fst_920_, v_size_916_);
lean_dec(v_fst_920_);
if v_isShared_924_ == 0 {
lean_ctor_set(v___x_923_, 1, v_a_932_);
lean_ctor_set(v___x_923_, 0, v___x_933_);
v___x_935_ = v___x_923_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_937_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_a_932_);
v___x_935_ = v_reuseFailAlloc_937_;
state = 2; continue;
}
} else {
let mut v_a_938_: *mut lean_object = core::ptr::null_mut(); let mut v___x_940_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_941_: u8 = 0; let mut v_isSharedCheck_945_: u8 = 0; 
lean_del_object(v___x_923_);
lean_dec(v_fst_920_);
v_a_938_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_945_ = (!lean_is_exclusive(v___x_931_)) as u8;
if v_isSharedCheck_945_ == 0 {
v___x_940_ = v___x_931_;
v_isShared_941_ = v_isSharedCheck_945_;
state = 3; continue;
} else {
lean_inc(v_a_938_);
lean_dec(v___x_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
state = 3; continue;
}
}
} else {
let mut v___x_947_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_924_ == 0 {
v___x_947_ = v___x_923_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_949_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_fst_920_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_snd_921_);
v___x_947_ = v_reuseFailAlloc_949_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2___redArg___boxed(mut v_size_951_: *mut lean_object, mut v_seed_952_: *mut lean_object, mut v_a_953_: *mut lean_object, mut v___y_954_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_955_: u64 = 0; let mut v_res_956_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_955_ = lean_unbox_uint64(v_seed_952_);
lean_dec_ref(v_seed_952_);
v_res_956_ = l___private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2___redArg(v_size_951_, v_seed_boxed_955_, v_a_953_);
lean_dec(v_size_951_);
return v_res_956_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertIfNewHit___lam__0(mut v_size_957_: *mut lean_object, mut v_seed_958_: u64, mut v___x_959_: *mut lean_object) -> *mut lean_object{
let mut v___x_961_: *mut lean_object = core::ptr::null_mut(); let mut v___x_963_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_964_: u8 = 0; let mut v___x_965_: *mut lean_object = core::ptr::null_mut(); let mut v___x_967_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_968_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_969_: u8 = 0; let mut v_unused_970_: *mut lean_object = core::ptr::null_mut(); let mut v_a_971_: *mut lean_object = core::ptr::null_mut(); let mut v___x_973_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_974_: u8 = 0; let mut v___x_976_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_977_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_978_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_961_ = l___private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2___redArg(v_size_957_, v_seed_958_, v___x_959_);
if lean_obj_tag(v___x_961_) == 0 {
let mut v___x_963_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_964_: u8 = 0; let mut v_isSharedCheck_969_: u8 = 0; 
v_isSharedCheck_969_ = (!lean_is_exclusive(v___x_961_)) as u8;
if v_isSharedCheck_969_ == 0 {
let mut v_unused_970_: *mut lean_object = core::ptr::null_mut(); 
v_unused_970_ = lean_ctor_get(v___x_961_, 0);
lean_dec(v_unused_970_);
v___x_963_ = v___x_961_;
v_isShared_964_ = v_isSharedCheck_969_;
state = 1; continue;
} else {
lean_dec(v___x_961_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_969_;
state = 1; continue;
}
} else {
let mut v_a_971_: *mut lean_object = core::ptr::null_mut(); let mut v___x_973_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_974_: u8 = 0; let mut v_isSharedCheck_978_: u8 = 0; 
v_a_971_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_978_ = (!lean_is_exclusive(v___x_961_)) as u8;
if v_isSharedCheck_978_ == 0 {
v___x_973_ = v___x_961_;
v_isShared_974_ = v_isSharedCheck_978_;
state = 3; continue;
} else {
lean_inc(v_a_971_);
lean_dec(v___x_961_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
state = 3; continue;
}
}
}
1 => {
v___x_965_ = lean_box(0);
if v_isShared_964_ == 0 {
lean_ctor_set(v___x_963_, 0, v___x_965_);
v___x_967_ = v___x_963_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_968_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
state = 2; continue;
}
}
3 => {
if v_isShared_974_ == 0 {
v___x_976_ = v___x_973_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_977_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertIfNewHit___lam__0___boxed(mut v_size_979_: *mut lean_object, mut v_seed_980_: *mut lean_object, mut v___x_981_: *mut lean_object, mut v___y_982_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_983_: u64 = 0; let mut v_res_984_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_983_ = lean_unbox_uint64(v_seed_980_);
lean_dec_ref(v_seed_980_);
v_res_984_ = l_benchInsertIfNewHit___lam__0(v_size_979_, v_seed_boxed_983_, v___x_981_);
lean_dec(v_size_979_);
return v_res_984_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertIfNewHit(mut v_seed_985_: u64, mut v_size_986_: *mut lean_object) -> *mut lean_object{
let mut v_map_988_: *mut lean_object = core::ptr::null_mut(); let mut v___x_989_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_990_: *mut lean_object = core::ptr::null_mut(); let mut v___x_991_: *mut lean_object = core::ptr::null_mut(); let mut v___x_992_: *mut lean_object = core::ptr::null_mut(); let mut v___f_993_: *mut lean_object = core::ptr::null_mut(); let mut v___x_994_: *mut lean_object = core::ptr::null_mut(); 
v_map_988_ = l_mkMapWithCap(v_seed_985_, v_size_986_);
v___x_989_ = lean_unsigned_to_nat(100);
v_todo_990_ = lean_nat_mul(v_size_986_, v___x_989_);
lean_inc(v_todo_990_);
v___x_991_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_991_, 0, v_todo_990_);
lean_ctor_set(v___x_991_, 1, v_map_988_);
v___x_992_ = lean_box_uint64(v_seed_985_);
v___f_993_ = lean_alloc_closure(l_benchInsertIfNewHit___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_993_, 0, v_size_986_);
lean_closure_set(v___f_993_, 1, v___x_992_);
lean_closure_set(v___f_993_, 2, v___x_991_);
v___x_994_ = l_timeNanos(v_todo_990_, v___f_993_);
return v___x_994_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertIfNewHit___boxed(mut v_seed_995_: *mut lean_object, mut v_size_996_: *mut lean_object, mut v_a_997_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_998_: u64 = 0; let mut v_res_999_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_998_ = lean_unbox_uint64(v_seed_995_);
lean_dec_ref(v_seed_995_);
v_res_999_ = l_benchInsertIfNewHit(v_seed_boxed_998_, v_size_996_);
return v_res_999_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00benchInsertIfNewHit_spec__0(mut v_00_u03b2_1000_: *mut lean_object, mut v_m_1001_: *mut lean_object, mut v_a_1002_: u64, mut v_b_1003_: *mut lean_object) -> *mut lean_object{
let mut v___x_1004_: *mut lean_object = core::ptr::null_mut(); 
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00benchInsertIfNewHit_spec__0___redArg(v_m_1001_, v_a_1002_, v_b_1003_);
return v___x_1004_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00benchInsertIfNewHit_spec__0___boxed(mut v_00_u03b2_1005_: *mut lean_object, mut v_m_1006_: *mut lean_object, mut v_a_1007_: *mut lean_object, mut v_b_1008_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_1009_: u64 = 0; let mut v_res_1010_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_1009_ = lean_unbox_uint64(v_a_1007_);
lean_dec_ref(v_a_1007_);
v_res_1010_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00benchInsertIfNewHit_spec__0(v_00_u03b2_1005_, v_m_1006_, v_a_boxed_1009_, v_b_1008_);
return v_res_1010_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1(mut v_size_1011_: *mut lean_object, mut v_inst_1012_: *mut lean_object, mut v_R_1013_: *mut lean_object, mut v_a_1014_: *mut lean_object, mut v_b_1015_: *mut lean_object, mut v_c_1016_: *mut lean_object) -> *mut lean_object{
let mut v___x_1018_: *mut lean_object = core::ptr::null_mut(); 
v___x_1018_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1___redArg(v_size_1011_, v_a_1014_, v_b_1015_);
return v___x_1018_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1___boxed(mut v_size_1019_: *mut lean_object, mut v_inst_1020_: *mut lean_object, mut v_R_1021_: *mut lean_object, mut v_a_1022_: *mut lean_object, mut v_b_1023_: *mut lean_object, mut v_c_1024_: *mut lean_object, mut v___y_1025_: *mut lean_object) -> *mut lean_object{
let mut v_res_1026_: *mut lean_object = core::ptr::null_mut(); 
v_res_1026_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertIfNewHit_spec__1(v_size_1019_, v_inst_1020_, v_R_1021_, v_a_1022_, v_b_1023_, v_c_1024_);
lean_dec(v_size_1019_);
return v_res_1026_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2(mut v_size_1027_: *mut lean_object, mut v_seed_1028_: u64, mut v_inst_1029_: *mut lean_object, mut v_a_1030_: *mut lean_object) -> *mut lean_object{
let mut v___x_1032_: *mut lean_object = core::ptr::null_mut(); 
v___x_1032_ = l___private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2___redArg(v_size_1027_, v_seed_1028_, v_a_1030_);
return v___x_1032_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2___boxed(mut v_size_1033_: *mut lean_object, mut v_seed_1034_: *mut lean_object, mut v_inst_1035_: *mut lean_object, mut v_a_1036_: *mut lean_object, mut v___y_1037_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1038_: u64 = 0; let mut v_res_1039_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1038_ = lean_unbox_uint64(v_seed_1034_);
lean_dec_ref(v_seed_1034_);
v_res_1039_ = l___private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2(v_size_1033_, v_seed_boxed_1038_, v_inst_1035_, v_a_1036_);
lean_dec(v_size_1033_);
return v_res_1039_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2_spec__2(mut v_seed_1040_: u64, mut v_size_1041_: *mut lean_object, mut v_inst_1042_: *mut lean_object, mut v_a_1043_: *mut lean_object) -> *mut lean_object{
let mut v___x_1045_: *mut lean_object = core::ptr::null_mut(); 
v___x_1045_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2_spec__2___redArg(v_seed_1040_, v_size_1041_, v_a_1043_);
return v___x_1045_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2_spec__2___boxed(mut v_seed_1046_: *mut lean_object, mut v_size_1047_: *mut lean_object, mut v_inst_1048_: *mut lean_object, mut v_a_1049_: *mut lean_object, mut v___y_1050_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1051_: u64 = 0; let mut v_res_1052_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1051_ = lean_unbox_uint64(v_seed_1046_);
lean_dec_ref(v_seed_1046_);
v_res_1052_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertIfNewHit_spec__2_spec__2(v_seed_boxed_1051_, v_size_1047_, v_inst_1048_, v_a_1049_);
lean_dec(v_size_1047_);
return v_res_1052_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0___redArg(mut v_size_1053_: *mut lean_object, mut v_a_1054_: *mut lean_object, mut v_b_1055_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_1057_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_1058_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1060_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1061_: u8 = 0; let mut v___x_1062_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1063_: u8 = 0; let mut v___x_1064_: u64 = 0; let mut v___x_1065_: u64 = 0; let mut v___x_1066_: u64 = 0; let mut v___x_1067_: u64 = 0; let mut v___x_1068_: *mut lean_object = core::ptr::null_mut(); let mut v_size_1069_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1070_: u8 = 0; let mut v___x_1071_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1072_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1073_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1074_: u64 = 0; let mut v___x_1075_: u64 = 0; let mut v___x_1076_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1077_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1079_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1081_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1082_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1083_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_1057_ = lean_ctor_get(v_a_1054_, 0);
v_inner_1058_ = lean_ctor_get(v_a_1054_, 1);
v_isSharedCheck_1083_ = (!lean_is_exclusive(v_a_1054_)) as u8;
if v_isSharedCheck_1083_ == 0 {
v___x_1060_ = v_a_1054_;
v_isShared_1061_ = v_isSharedCheck_1083_;
state = 1; continue;
} else {
lean_inc(v_inner_1058_);
lean_inc(v_countdown_1057_);
lean_dec(v_a_1054_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1083_;
state = 1; continue;
}
}
1 => {
v___x_1062_ = lean_unsigned_to_nat(1);
v___x_1063_ = lean_nat_dec_eq(v_countdown_1057_, v___x_1062_);
if v___x_1063_ == 0 {
let mut v___x_1064_: u64 = 0; let mut v___x_1065_: u64 = 0; let mut v___x_1066_: u64 = 0; let mut v___x_1067_: u64 = 0; let mut v___x_1068_: *mut lean_object = core::ptr::null_mut(); let mut v_size_1069_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1070_: u8 = 0; 
v___x_1064_ = 1u64;
v___x_1065_ = lean_unbox_uint64(v_inner_1058_);
v___x_1066_ = lean_uint64_add(v___x_1065_, v___x_1064_);
v___x_1067_ = lean_unbox_uint64(v_inner_1058_);
v___x_1068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0___redArg(v_b_1055_, v___x_1067_, v_inner_1058_);
v_size_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_size_1069_);
v___x_1070_ = lean_nat_dec_eq(v_size_1069_, v_size_1053_);
lean_dec(v_size_1069_);
if v___x_1070_ == 0 {
let mut v___x_1071_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1072_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1073_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v___x_1068_);
lean_del_object(v___x_1060_);
lean_dec(v_countdown_1057_);
v___x_1071_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_1072_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
} else {
let mut v___x_1074_: u64 = 0; let mut v___x_1075_: u64 = 0; let mut v___x_1076_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1077_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1079_: *mut lean_object = core::ptr::null_mut(); 
v___x_1074_ = 3787392781u64;
v___x_1075_ = lean_uint64_mul(v___x_1066_, v___x_1074_);
v___x_1076_ = lean_nat_sub(v_countdown_1057_, v___x_1062_);
lean_dec(v_countdown_1057_);
v___x_1077_ = lean_box_uint64(v___x_1075_);
if v_isShared_1061_ == 0 {
lean_ctor_set(v___x_1060_, 1, v___x_1077_);
lean_ctor_set(v___x_1060_, 0, v___x_1076_);
v___x_1079_ = v___x_1060_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1081_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1081_;
state = 2; continue;
}
}
} else {
let mut v___x_1082_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_1060_);
lean_dec(v_inner_1058_);
lean_dec(v_countdown_1057_);
v___x_1082_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1082_, 0, v_b_1055_);
return v___x_1082_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0___redArg___boxed(mut v_size_1084_: *mut lean_object, mut v_a_1085_: *mut lean_object, mut v_b_1086_: *mut lean_object, mut v___y_1087_: *mut lean_object) -> *mut lean_object{
let mut v_res_1088_: *mut lean_object = core::ptr::null_mut(); 
v_res_1088_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0___redArg(v_size_1084_, v_a_1085_, v_b_1086_);
lean_dec(v_size_1084_);
return v_res_1088_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1_spec__1___redArg(mut v_seed_1089_: u64, mut v_size_1090_: *mut lean_object, mut v_a_1091_: *mut lean_object) -> *mut lean_object{
let mut v_fst_1093_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1094_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1096_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1097_: u8 = 0; let mut v___x_1098_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1099_: u8 = 0; let mut v___x_1100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1104_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1108_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1110_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1113_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1114_: u8 = 0; let mut v___x_1116_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1117_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1118_: u8 = 0; let mut v___x_1120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1121_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1122_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1123_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_1093_ = lean_ctor_get(v_a_1091_, 0);
v_snd_1094_ = lean_ctor_get(v_a_1091_, 1);
v_isSharedCheck_1123_ = (!lean_is_exclusive(v_a_1091_)) as u8;
if v_isSharedCheck_1123_ == 0 {
v___x_1096_ = v_a_1091_;
v_isShared_1097_ = v_isSharedCheck_1123_;
state = 1; continue;
} else {
lean_inc(v_snd_1094_);
lean_inc(v_fst_1093_);
lean_dec(v_a_1091_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1123_;
state = 1; continue;
}
}
1 => {
v___x_1098_ = lean_unsigned_to_nat(0);
v___x_1099_ = lean_nat_dec_eq(v_fst_1093_, v___x_1098_);
if v___x_1099_ == 0 {
let mut v___x_1100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1104_: *mut lean_object = core::ptr::null_mut(); 
v___x_1100_ = lean_unsigned_to_nat(1);
v___x_1101_ = lean_nat_add(v_size_1090_, v___x_1100_);
v___x_1102_ = lean_box_uint64(v_seed_1089_);
v___x_1103_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0___redArg(v_size_1090_, v___x_1103_, v_snd_1094_);
if lean_obj_tag(v___x_1104_) == 0 {
let mut v_a_1105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1108_: *mut lean_object = core::ptr::null_mut(); 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = lean_nat_sub(v_fst_1093_, v_size_1090_);
lean_dec(v_fst_1093_);
if v_isShared_1097_ == 0 {
lean_ctor_set(v___x_1096_, 1, v_a_1105_);
lean_ctor_set(v___x_1096_, 0, v___x_1106_);
v___x_1108_ = v___x_1096_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1110_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_a_1105_);
v___x_1108_ = v_reuseFailAlloc_1110_;
state = 2; continue;
}
} else {
let mut v_a_1111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1113_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1114_: u8 = 0; let mut v_isSharedCheck_1118_: u8 = 0; 
lean_del_object(v___x_1096_);
lean_dec(v_fst_1093_);
v_a_1111_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1118_ = (!lean_is_exclusive(v___x_1104_)) as u8;
if v_isSharedCheck_1118_ == 0 {
v___x_1113_ = v___x_1104_;
v_isShared_1114_ = v_isSharedCheck_1118_;
state = 3; continue;
} else {
lean_inc(v_a_1111_);
lean_dec(v___x_1104_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
state = 3; continue;
}
}
} else {
let mut v___x_1120_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_1097_ == 0 {
v___x_1120_ = v___x_1096_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_1122_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_fst_1093_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_snd_1094_);
v___x_1120_ = v_reuseFailAlloc_1122_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1_spec__1___redArg___boxed(mut v_seed_1124_: *mut lean_object, mut v_size_1125_: *mut lean_object, mut v_a_1126_: *mut lean_object, mut v___y_1127_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1128_: u64 = 0; let mut v_res_1129_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1128_ = lean_unbox_uint64(v_seed_1124_);
lean_dec_ref(v_seed_1124_);
v_res_1129_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1_spec__1___redArg(v_seed_boxed_1128_, v_size_1125_, v_a_1126_);
lean_dec(v_size_1125_);
return v_res_1129_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1___redArg(mut v_size_1130_: *mut lean_object, mut v_seed_1131_: u64, mut v_a_1132_: *mut lean_object) -> *mut lean_object{
let mut v_fst_1134_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1137_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1138_: u8 = 0; let mut v___x_1139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1140_: u8 = 0; let mut v___x_1141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1145_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1150_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1151_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1154_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1155_: u8 = 0; let mut v___x_1157_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1158_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1159_: u8 = 0; let mut v___x_1161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1162_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1163_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1164_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_1134_ = lean_ctor_get(v_a_1132_, 0);
v_snd_1135_ = lean_ctor_get(v_a_1132_, 1);
v_isSharedCheck_1164_ = (!lean_is_exclusive(v_a_1132_)) as u8;
if v_isSharedCheck_1164_ == 0 {
v___x_1137_ = v_a_1132_;
v_isShared_1138_ = v_isSharedCheck_1164_;
state = 1; continue;
} else {
lean_inc(v_snd_1135_);
lean_inc(v_fst_1134_);
lean_dec(v_a_1132_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1164_;
state = 1; continue;
}
}
1 => {
v___x_1139_ = lean_unsigned_to_nat(0);
v___x_1140_ = lean_nat_dec_eq(v_fst_1134_, v___x_1139_);
if v___x_1140_ == 0 {
let mut v___x_1141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1145_: *mut lean_object = core::ptr::null_mut(); 
v___x_1141_ = lean_unsigned_to_nat(1);
v___x_1142_ = lean_nat_add(v_size_1130_, v___x_1141_);
v___x_1143_ = lean_box_uint64(v_seed_1131_);
v___x_1144_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0___redArg(v_size_1130_, v___x_1144_, v_snd_1135_);
if lean_obj_tag(v___x_1145_) == 0 {
let mut v_a_1146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1149_: *mut lean_object = core::ptr::null_mut(); 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_nat_sub(v_fst_1134_, v_size_1130_);
lean_dec(v_fst_1134_);
if v_isShared_1138_ == 0 {
lean_ctor_set(v___x_1137_, 1, v_a_1146_);
lean_ctor_set(v___x_1137_, 0, v___x_1147_);
v___x_1149_ = v___x_1137_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1151_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_a_1146_);
v___x_1149_ = v_reuseFailAlloc_1151_;
state = 2; continue;
}
} else {
let mut v_a_1152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1154_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1155_: u8 = 0; let mut v_isSharedCheck_1159_: u8 = 0; 
lean_del_object(v___x_1137_);
lean_dec(v_fst_1134_);
v_a_1152_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1159_ = (!lean_is_exclusive(v___x_1145_)) as u8;
if v_isSharedCheck_1159_ == 0 {
v___x_1154_ = v___x_1145_;
v_isShared_1155_ = v_isSharedCheck_1159_;
state = 3; continue;
} else {
lean_inc(v_a_1152_);
lean_dec(v___x_1145_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
state = 3; continue;
}
}
} else {
let mut v___x_1161_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_1138_ == 0 {
v___x_1161_ = v___x_1137_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_1163_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_fst_1134_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_snd_1135_);
v___x_1161_ = v_reuseFailAlloc_1163_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1___redArg___boxed(mut v_size_1165_: *mut lean_object, mut v_seed_1166_: *mut lean_object, mut v_a_1167_: *mut lean_object, mut v___y_1168_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1169_: u64 = 0; let mut v_res_1170_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1169_ = lean_unbox_uint64(v_seed_1166_);
lean_dec_ref(v_seed_1166_);
v_res_1170_ = l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1___redArg(v_size_1165_, v_seed_boxed_1169_, v_a_1167_);
lean_dec(v_size_1165_);
return v_res_1170_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertHit___lam__0(mut v_size_1171_: *mut lean_object, mut v_seed_1172_: u64, mut v___x_1173_: *mut lean_object) -> *mut lean_object{
let mut v___x_1175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1177_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1178_: u8 = 0; let mut v___x_1179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1181_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1182_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1183_: u8 = 0; let mut v_unused_1184_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1185_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1187_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1188_: u8 = 0; let mut v___x_1190_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1191_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1192_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1175_ = l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1___redArg(v_size_1171_, v_seed_1172_, v___x_1173_);
if lean_obj_tag(v___x_1175_) == 0 {
let mut v___x_1177_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1178_: u8 = 0; let mut v_isSharedCheck_1183_: u8 = 0; 
v_isSharedCheck_1183_ = (!lean_is_exclusive(v___x_1175_)) as u8;
if v_isSharedCheck_1183_ == 0 {
let mut v_unused_1184_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1184_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1184_);
v___x_1177_ = v___x_1175_;
v_isShared_1178_ = v_isSharedCheck_1183_;
state = 1; continue;
} else {
lean_dec(v___x_1175_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
state = 1; continue;
}
} else {
let mut v_a_1185_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1187_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1188_: u8 = 0; let mut v_isSharedCheck_1192_: u8 = 0; 
v_a_1185_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1192_ = (!lean_is_exclusive(v___x_1175_)) as u8;
if v_isSharedCheck_1192_ == 0 {
v___x_1187_ = v___x_1175_;
v_isShared_1188_ = v_isSharedCheck_1192_;
state = 3; continue;
} else {
lean_inc(v_a_1185_);
lean_dec(v___x_1175_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
state = 3; continue;
}
}
}
1 => {
v___x_1179_ = lean_box(0);
if v_isShared_1178_ == 0 {
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1182_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
state = 2; continue;
}
}
3 => {
if v_isShared_1188_ == 0 {
v___x_1190_ = v___x_1187_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1191_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertHit___lam__0___boxed(mut v_size_1193_: *mut lean_object, mut v_seed_1194_: *mut lean_object, mut v___x_1195_: *mut lean_object, mut v___y_1196_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1197_: u64 = 0; let mut v_res_1198_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1197_ = lean_unbox_uint64(v_seed_1194_);
lean_dec_ref(v_seed_1194_);
v_res_1198_ = l_benchInsertHit___lam__0(v_size_1193_, v_seed_boxed_1197_, v___x_1195_);
lean_dec(v_size_1193_);
return v_res_1198_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertHit(mut v_seed_1199_: u64, mut v_size_1200_: *mut lean_object) -> *mut lean_object{
let mut v_map_1202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1203_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1206_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1208_: *mut lean_object = core::ptr::null_mut(); 
v_map_1202_ = l_mkMapWithCap(v_seed_1199_, v_size_1200_);
v___x_1203_ = lean_unsigned_to_nat(100);
v_todo_1204_ = lean_nat_mul(v_size_1200_, v___x_1203_);
lean_inc(v_todo_1204_);
v___x_1205_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1205_, 0, v_todo_1204_);
lean_ctor_set(v___x_1205_, 1, v_map_1202_);
v___x_1206_ = lean_box_uint64(v_seed_1199_);
v___f_1207_ = lean_alloc_closure(l_benchInsertHit___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_1207_, 0, v_size_1200_);
lean_closure_set(v___f_1207_, 1, v___x_1206_);
lean_closure_set(v___f_1207_, 2, v___x_1205_);
v___x_1208_ = l_timeNanos(v_todo_1204_, v___f_1207_);
return v___x_1208_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertHit___boxed(mut v_seed_1209_: *mut lean_object, mut v_size_1210_: *mut lean_object, mut v_a_1211_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1212_: u64 = 0; let mut v_res_1213_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1212_ = lean_unbox_uint64(v_seed_1209_);
lean_dec_ref(v_seed_1209_);
v_res_1213_ = l_benchInsertHit(v_seed_boxed_1212_, v_size_1210_);
return v_res_1213_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0(mut v_size_1214_: *mut lean_object, mut v_inst_1215_: *mut lean_object, mut v_R_1216_: *mut lean_object, mut v_a_1217_: *mut lean_object, mut v_b_1218_: *mut lean_object, mut v_c_1219_: *mut lean_object) -> *mut lean_object{
let mut v___x_1221_: *mut lean_object = core::ptr::null_mut(); 
v___x_1221_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0___redArg(v_size_1214_, v_a_1217_, v_b_1218_);
return v___x_1221_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0___boxed(mut v_size_1222_: *mut lean_object, mut v_inst_1223_: *mut lean_object, mut v_R_1224_: *mut lean_object, mut v_a_1225_: *mut lean_object, mut v_b_1226_: *mut lean_object, mut v_c_1227_: *mut lean_object, mut v___y_1228_: *mut lean_object) -> *mut lean_object{
let mut v_res_1229_: *mut lean_object = core::ptr::null_mut(); 
v_res_1229_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__0(v_size_1222_, v_inst_1223_, v_R_1224_, v_a_1225_, v_b_1226_, v_c_1227_);
lean_dec(v_size_1222_);
return v_res_1229_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1(mut v_size_1230_: *mut lean_object, mut v_seed_1231_: u64, mut v_inst_1232_: *mut lean_object, mut v_a_1233_: *mut lean_object) -> *mut lean_object{
let mut v___x_1235_: *mut lean_object = core::ptr::null_mut(); 
v___x_1235_ = l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1___redArg(v_size_1230_, v_seed_1231_, v_a_1233_);
return v___x_1235_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1___boxed(mut v_size_1236_: *mut lean_object, mut v_seed_1237_: *mut lean_object, mut v_inst_1238_: *mut lean_object, mut v_a_1239_: *mut lean_object, mut v___y_1240_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1241_: u64 = 0; let mut v_res_1242_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1241_ = lean_unbox_uint64(v_seed_1237_);
lean_dec_ref(v_seed_1237_);
v_res_1242_ = l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1(v_size_1236_, v_seed_boxed_1241_, v_inst_1238_, v_a_1239_);
lean_dec(v_size_1236_);
return v_res_1242_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1_spec__1(mut v_seed_1243_: u64, mut v_size_1244_: *mut lean_object, mut v_inst_1245_: *mut lean_object, mut v_a_1246_: *mut lean_object) -> *mut lean_object{
let mut v___x_1248_: *mut lean_object = core::ptr::null_mut(); 
v___x_1248_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1_spec__1___redArg(v_seed_1243_, v_size_1244_, v_a_1246_);
return v___x_1248_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1_spec__1___boxed(mut v_seed_1249_: *mut lean_object, mut v_size_1250_: *mut lean_object, mut v_inst_1251_: *mut lean_object, mut v_a_1252_: *mut lean_object, mut v___y_1253_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1254_: u64 = 0; let mut v_res_1255_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1254_ = lean_unbox_uint64(v_seed_1249_);
lean_dec_ref(v_seed_1249_);
v_res_1255_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__1_spec__1(v_seed_boxed_1254_, v_size_1250_, v_inst_1251_, v_a_1252_);
lean_dec(v_size_1250_);
return v_res_1255_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0___redArg(mut v_size_1256_: *mut lean_object, mut v_a_1257_: *mut lean_object, mut v_b_1258_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_1260_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_1261_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1263_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1264_: u8 = 0; let mut v___x_1265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1266_: u8 = 0; let mut v___x_1267_: u64 = 0; let mut v___x_1268_: u64 = 0; let mut v___x_1269_: u64 = 0; let mut v___x_1270_: u64 = 0; let mut v___x_1271_: *mut lean_object = core::ptr::null_mut(); let mut v_size_1272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1273_: u8 = 0; let mut v___x_1274_: u64 = 0; let mut v___x_1275_: u64 = 0; let mut v___x_1276_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1277_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1279_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1282_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1285_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1286_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_1260_ = lean_ctor_get(v_a_1257_, 0);
v_inner_1261_ = lean_ctor_get(v_a_1257_, 1);
v_isSharedCheck_1286_ = (!lean_is_exclusive(v_a_1257_)) as u8;
if v_isSharedCheck_1286_ == 0 {
v___x_1263_ = v_a_1257_;
v_isShared_1264_ = v_isSharedCheck_1286_;
state = 1; continue;
} else {
lean_inc(v_inner_1261_);
lean_inc(v_countdown_1260_);
lean_dec(v_a_1257_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1286_;
state = 1; continue;
}
}
1 => {
v___x_1265_ = lean_unsigned_to_nat(1);
v___x_1266_ = lean_nat_dec_eq(v_countdown_1260_, v___x_1265_);
if v___x_1266_ == 0 {
let mut v___x_1267_: u64 = 0; let mut v___x_1268_: u64 = 0; let mut v___x_1269_: u64 = 0; let mut v___x_1270_: u64 = 0; let mut v___x_1271_: *mut lean_object = core::ptr::null_mut(); let mut v_size_1272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1273_: u8 = 0; 
v___x_1267_ = 1u64;
v___x_1268_ = lean_unbox_uint64(v_inner_1261_);
v___x_1269_ = lean_uint64_add(v___x_1268_, v___x_1267_);
v___x_1270_ = lean_unbox_uint64(v_inner_1261_);
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0___redArg(v_b_1258_, v___x_1270_, v_inner_1261_);
v_size_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_size_1272_);
v___x_1273_ = lean_nat_dec_lt(v_size_1256_, v_size_1272_);
lean_dec(v_size_1272_);
if v___x_1273_ == 0 {
let mut v___x_1274_: u64 = 0; let mut v___x_1275_: u64 = 0; let mut v___x_1276_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1277_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1279_: *mut lean_object = core::ptr::null_mut(); 
v___x_1274_ = 3787392781u64;
v___x_1275_ = lean_uint64_mul(v___x_1269_, v___x_1274_);
v___x_1276_ = lean_nat_sub(v_countdown_1260_, v___x_1265_);
lean_dec(v_countdown_1260_);
v___x_1277_ = lean_box_uint64(v___x_1275_);
if v_isShared_1264_ == 0 {
lean_ctor_set(v___x_1263_, 1, v___x_1277_);
lean_ctor_set(v___x_1263_, 0, v___x_1276_);
v___x_1279_ = v___x_1263_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1281_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1281_;
state = 2; continue;
}
} else {
let mut v___x_1282_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1284_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v___x_1271_);
lean_del_object(v___x_1263_);
lean_dec(v_countdown_1260_);
v___x_1282_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_1283_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
} else {
let mut v___x_1285_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_1263_);
lean_dec(v_inner_1261_);
lean_dec(v_countdown_1260_);
v___x_1285_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1285_, 0, v_b_1258_);
return v___x_1285_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0___redArg___boxed(mut v_size_1287_: *mut lean_object, mut v_a_1288_: *mut lean_object, mut v_b_1289_: *mut lean_object, mut v___y_1290_: *mut lean_object) -> *mut lean_object{
let mut v_res_1291_: *mut lean_object = core::ptr::null_mut(); 
v_res_1291_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0___redArg(v_size_1287_, v_a_1288_, v_b_1289_);
lean_dec(v_size_1287_);
return v_res_1291_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1_spec__1___redArg(mut v_seed_1292_: u64, mut v_size_1293_: *mut lean_object, mut v_a_1294_: *mut lean_object) -> *mut lean_object{
let mut v___x_1296_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1297_: u8 = 0; let mut v___x_1298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1301_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1306_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1307_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1311_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1312_: u8 = 0; let mut v___x_1314_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1315_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1316_: u8 = 0; let mut v___x_1317_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1296_ = lean_unsigned_to_nat(0);
v___x_1297_ = lean_nat_dec_eq(v_a_1294_, v___x_1296_);
if v___x_1297_ == 0 {
let mut v___x_1298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1301_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1306_: *mut lean_object = core::ptr::null_mut(); 
v___x_1298_ = lean_unsigned_to_nat(16);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_mk_array(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1301_, 0, v___x_1296_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_unsigned_to_nat(1);
v___x_1303_ = lean_nat_add(v_size_1293_, v___x_1302_);
v___x_1304_ = lean_box_uint64(v_seed_1292_);
v___x_1305_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0___redArg(v_size_1293_, v___x_1305_, v___x_1301_);
if lean_obj_tag(v___x_1306_) == 0 {
let mut v___x_1307_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1306_, 1);
v___x_1307_ = lean_nat_sub(v_a_1294_, v_size_1293_);
lean_dec(v_a_1294_);
v_a_1294_ = v___x_1307_;
state = 0; continue;
} else {
let mut v_a_1309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1311_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1312_: u8 = 0; let mut v_isSharedCheck_1316_: u8 = 0; 
lean_dec(v_a_1294_);
v_a_1309_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1316_ = (!lean_is_exclusive(v___x_1306_)) as u8;
if v_isSharedCheck_1316_ == 0 {
v___x_1311_ = v___x_1306_;
v_isShared_1312_ = v_isSharedCheck_1316_;
state = 1; continue;
} else {
lean_inc(v_a_1309_);
lean_dec(v___x_1306_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
state = 1; continue;
}
}
} else {
let mut v___x_1317_: *mut lean_object = core::ptr::null_mut(); 
v___x_1317_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1317_, 0, v_a_1294_);
return v___x_1317_;
}
}
1 => {
if v_isShared_1312_ == 0 {
v___x_1314_ = v___x_1311_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1315_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1_spec__1___redArg___boxed(mut v_seed_1318_: *mut lean_object, mut v_size_1319_: *mut lean_object, mut v_a_1320_: *mut lean_object, mut v___y_1321_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1322_: u64 = 0; let mut v_res_1323_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1322_ = lean_unbox_uint64(v_seed_1318_);
lean_dec_ref(v_seed_1318_);
v_res_1323_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1_spec__1___redArg(v_seed_boxed_1322_, v_size_1319_, v_a_1320_);
lean_dec(v_size_1319_);
return v_res_1323_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1___redArg(mut v_size_1324_: *mut lean_object, mut v_seed_1325_: u64, mut v_a_1326_: *mut lean_object) -> *mut lean_object{
let mut v___x_1328_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1329_: u8 = 0; let mut v___x_1330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1336_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1339_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1340_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1343_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1344_: u8 = 0; let mut v___x_1346_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1347_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1348_: u8 = 0; let mut v___x_1349_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1328_ = lean_unsigned_to_nat(0);
v___x_1329_ = lean_nat_dec_eq(v_a_1326_, v___x_1328_);
if v___x_1329_ == 0 {
let mut v___x_1330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1336_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1338_: *mut lean_object = core::ptr::null_mut(); 
v___x_1330_ = lean_unsigned_to_nat(16);
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_mk_array(v___x_1330_, v___x_1331_);
v___x_1333_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1333_, 0, v___x_1328_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = lean_unsigned_to_nat(1);
v___x_1335_ = lean_nat_add(v_size_1324_, v___x_1334_);
v___x_1336_ = lean_box_uint64(v_seed_1325_);
v___x_1337_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0___redArg(v_size_1324_, v___x_1337_, v___x_1333_);
if lean_obj_tag(v___x_1338_) == 0 {
let mut v___x_1339_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1340_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1338_, 1);
v___x_1339_ = lean_nat_sub(v_a_1326_, v_size_1324_);
lean_dec(v_a_1326_);
v___x_1340_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1_spec__1___redArg(v_seed_1325_, v_size_1324_, v___x_1339_);
return v___x_1340_;
} else {
let mut v_a_1341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1343_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1344_: u8 = 0; let mut v_isSharedCheck_1348_: u8 = 0; 
lean_dec(v_a_1326_);
v_a_1341_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1348_ = (!lean_is_exclusive(v___x_1338_)) as u8;
if v_isSharedCheck_1348_ == 0 {
v___x_1343_ = v___x_1338_;
v_isShared_1344_ = v_isSharedCheck_1348_;
state = 1; continue;
} else {
lean_inc(v_a_1341_);
lean_dec(v___x_1338_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
state = 1; continue;
}
}
} else {
let mut v___x_1349_: *mut lean_object = core::ptr::null_mut(); 
v___x_1349_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1349_, 0, v_a_1326_);
return v___x_1349_;
}
}
1 => {
if v_isShared_1344_ == 0 {
v___x_1346_ = v___x_1343_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1347_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1___redArg___boxed(mut v_size_1350_: *mut lean_object, mut v_seed_1351_: *mut lean_object, mut v_a_1352_: *mut lean_object, mut v___y_1353_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1354_: u64 = 0; let mut v_res_1355_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1354_ = lean_unbox_uint64(v_seed_1351_);
lean_dec_ref(v_seed_1351_);
v_res_1355_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1___redArg(v_size_1350_, v_seed_boxed_1354_, v_a_1352_);
lean_dec(v_size_1350_);
return v_res_1355_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmpty___lam__0(mut v_size_1356_: *mut lean_object, mut v_seed_1357_: u64, mut v_todo_1358_: *mut lean_object) -> *mut lean_object{
let mut v___x_1360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1362_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1363_: u8 = 0; let mut v___x_1364_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1366_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1367_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1368_: u8 = 0; let mut v_unused_1369_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1372_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1373_: u8 = 0; let mut v___x_1375_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1376_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1377_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1360_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1___redArg(v_size_1356_, v_seed_1357_, v_todo_1358_);
if lean_obj_tag(v___x_1360_) == 0 {
let mut v___x_1362_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1363_: u8 = 0; let mut v_isSharedCheck_1368_: u8 = 0; 
v_isSharedCheck_1368_ = (!lean_is_exclusive(v___x_1360_)) as u8;
if v_isSharedCheck_1368_ == 0 {
let mut v_unused_1369_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1369_ = lean_ctor_get(v___x_1360_, 0);
lean_dec(v_unused_1369_);
v___x_1362_ = v___x_1360_;
v_isShared_1363_ = v_isSharedCheck_1368_;
state = 1; continue;
} else {
lean_dec(v___x_1360_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
state = 1; continue;
}
} else {
let mut v_a_1370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1372_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1373_: u8 = 0; let mut v_isSharedCheck_1377_: u8 = 0; 
v_a_1370_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1377_ = (!lean_is_exclusive(v___x_1360_)) as u8;
if v_isSharedCheck_1377_ == 0 {
v___x_1372_ = v___x_1360_;
v_isShared_1373_ = v_isSharedCheck_1377_;
state = 3; continue;
} else {
lean_inc(v_a_1370_);
lean_dec(v___x_1360_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
state = 3; continue;
}
}
}
1 => {
v___x_1364_ = lean_box(0);
if v_isShared_1363_ == 0 {
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1366_ = v___x_1362_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1367_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
state = 2; continue;
}
}
3 => {
if v_isShared_1373_ == 0 {
v___x_1375_ = v___x_1372_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1376_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmpty___lam__0___boxed(mut v_size_1378_: *mut lean_object, mut v_seed_1379_: *mut lean_object, mut v_todo_1380_: *mut lean_object, mut v___y_1381_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1382_: u64 = 0; let mut v_res_1383_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1382_ = lean_unbox_uint64(v_seed_1379_);
lean_dec_ref(v_seed_1379_);
v_res_1383_ = l_benchInsertMissEmpty___lam__0(v_size_1378_, v_seed_boxed_1382_, v_todo_1380_);
lean_dec(v_size_1378_);
return v_res_1383_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmpty(mut v_seed_1384_: u64, mut v_size_1385_: *mut lean_object) -> *mut lean_object{
let mut v___x_1387_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1388_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1389_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1390_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1391_: *mut lean_object = core::ptr::null_mut(); 
v___x_1387_ = lean_unsigned_to_nat(100);
v_todo_1388_ = lean_nat_mul(v_size_1385_, v___x_1387_);
v___x_1389_ = lean_box_uint64(v_seed_1384_);
lean_inc(v_todo_1388_);
v___f_1390_ = lean_alloc_closure(l_benchInsertMissEmpty___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_1390_, 0, v_size_1385_);
lean_closure_set(v___f_1390_, 1, v___x_1389_);
lean_closure_set(v___f_1390_, 2, v_todo_1388_);
v___x_1391_ = l_timeNanos(v_todo_1388_, v___f_1390_);
return v___x_1391_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmpty___boxed(mut v_seed_1392_: *mut lean_object, mut v_size_1393_: *mut lean_object, mut v_a_1394_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1395_: u64 = 0; let mut v_res_1396_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1395_ = lean_unbox_uint64(v_seed_1392_);
lean_dec_ref(v_seed_1392_);
v_res_1396_ = l_benchInsertMissEmpty(v_seed_boxed_1395_, v_size_1393_);
return v_res_1396_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0(mut v_size_1397_: *mut lean_object, mut v_inst_1398_: *mut lean_object, mut v_R_1399_: *mut lean_object, mut v_a_1400_: *mut lean_object, mut v_b_1401_: *mut lean_object, mut v_c_1402_: *mut lean_object) -> *mut lean_object{
let mut v___x_1404_: *mut lean_object = core::ptr::null_mut(); 
v___x_1404_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0___redArg(v_size_1397_, v_a_1400_, v_b_1401_);
return v___x_1404_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0___boxed(mut v_size_1405_: *mut lean_object, mut v_inst_1406_: *mut lean_object, mut v_R_1407_: *mut lean_object, mut v_a_1408_: *mut lean_object, mut v_b_1409_: *mut lean_object, mut v_c_1410_: *mut lean_object, mut v___y_1411_: *mut lean_object) -> *mut lean_object{
let mut v_res_1412_: *mut lean_object = core::ptr::null_mut(); 
v_res_1412_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0(v_size_1405_, v_inst_1406_, v_R_1407_, v_a_1408_, v_b_1409_, v_c_1410_);
lean_dec(v_size_1405_);
return v_res_1412_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1(mut v_size_1413_: *mut lean_object, mut v_seed_1414_: u64, mut v_inst_1415_: *mut lean_object, mut v_a_1416_: *mut lean_object) -> *mut lean_object{
let mut v___x_1418_: *mut lean_object = core::ptr::null_mut(); 
v___x_1418_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1___redArg(v_size_1413_, v_seed_1414_, v_a_1416_);
return v___x_1418_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1___boxed(mut v_size_1419_: *mut lean_object, mut v_seed_1420_: *mut lean_object, mut v_inst_1421_: *mut lean_object, mut v_a_1422_: *mut lean_object, mut v___y_1423_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1424_: u64 = 0; let mut v_res_1425_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1424_ = lean_unbox_uint64(v_seed_1420_);
lean_dec_ref(v_seed_1420_);
v_res_1425_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1(v_size_1419_, v_seed_boxed_1424_, v_inst_1421_, v_a_1422_);
lean_dec(v_size_1419_);
return v_res_1425_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1_spec__1(mut v_seed_1426_: u64, mut v_size_1427_: *mut lean_object, mut v_inst_1428_: *mut lean_object, mut v_a_1429_: *mut lean_object) -> *mut lean_object{
let mut v___x_1431_: *mut lean_object = core::ptr::null_mut(); 
v___x_1431_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1_spec__1___redArg(v_seed_1426_, v_size_1427_, v_a_1429_);
return v___x_1431_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1_spec__1___boxed(mut v_seed_1432_: *mut lean_object, mut v_size_1433_: *mut lean_object, mut v_inst_1434_: *mut lean_object, mut v_a_1435_: *mut lean_object, mut v___y_1436_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1437_: u64 = 0; let mut v_res_1438_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1437_ = lean_unbox_uint64(v_seed_1432_);
lean_dec_ref(v_seed_1432_);
v_res_1438_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__1_spec__1(v_seed_boxed_1437_, v_size_1433_, v_inst_1434_, v_a_1435_);
lean_dec(v_size_1433_);
return v_res_1438_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyWithCapacity_spec__0___redArg(mut v_size_1439_: *mut lean_object, mut v_seed_1440_: u64, mut v_a_1441_: *mut lean_object) -> *mut lean_object{
let mut v___x_1443_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1444_: u8 = 0; let mut v___x_1445_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1447_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1453_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1457_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1458_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1460_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1462_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1463_: u8 = 0; let mut v___x_1465_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1466_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1467_: u8 = 0; let mut v___x_1468_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1443_ = lean_unsigned_to_nat(0);
v___x_1444_ = lean_nat_dec_eq(v_a_1441_, v___x_1443_);
if v___x_1444_ == 0 {
let mut v___x_1445_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1447_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1450_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1453_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1457_: *mut lean_object = core::ptr::null_mut(); 
v___x_1445_ = lean_unsigned_to_nat(4);
v___x_1446_ = lean_nat_mul(v_size_1439_, v___x_1445_);
v___x_1447_ = lean_unsigned_to_nat(3);
v___x_1448_ = lean_nat_div(v___x_1446_, v___x_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = l_Nat_nextPowerOfTwo(v___x_1448_);
lean_dec(v___x_1448_);
v___x_1450_ = lean_box(0);
v___x_1451_ = lean_mk_array(v___x_1449_, v___x_1450_);
v___x_1452_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1452_, 0, v___x_1443_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_unsigned_to_nat(1);
v___x_1454_ = lean_nat_add(v_size_1439_, v___x_1453_);
v___x_1455_ = lean_box_uint64(v_seed_1440_);
v___x_1456_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmpty_spec__0___redArg(v_size_1439_, v___x_1456_, v___x_1452_);
if lean_obj_tag(v___x_1457_) == 0 {
let mut v___x_1458_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1457_, 1);
v___x_1458_ = lean_nat_sub(v_a_1441_, v_size_1439_);
lean_dec(v_a_1441_);
v_a_1441_ = v___x_1458_;
state = 0; continue;
} else {
let mut v_a_1460_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1462_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1463_: u8 = 0; let mut v_isSharedCheck_1467_: u8 = 0; 
lean_dec(v_a_1441_);
v_a_1460_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1467_ = (!lean_is_exclusive(v___x_1457_)) as u8;
if v_isSharedCheck_1467_ == 0 {
v___x_1462_ = v___x_1457_;
v_isShared_1463_ = v_isSharedCheck_1467_;
state = 1; continue;
} else {
lean_inc(v_a_1460_);
lean_dec(v___x_1457_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
state = 1; continue;
}
}
} else {
let mut v___x_1468_: *mut lean_object = core::ptr::null_mut(); 
v___x_1468_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1468_, 0, v_a_1441_);
return v___x_1468_;
}
}
1 => {
if v_isShared_1463_ == 0 {
v___x_1465_ = v___x_1462_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1466_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyWithCapacity_spec__0___redArg___boxed(mut v_size_1469_: *mut lean_object, mut v_seed_1470_: *mut lean_object, mut v_a_1471_: *mut lean_object, mut v___y_1472_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1473_: u64 = 0; let mut v_res_1474_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1473_ = lean_unbox_uint64(v_seed_1470_);
lean_dec_ref(v_seed_1470_);
v_res_1474_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyWithCapacity_spec__0___redArg(v_size_1469_, v_seed_boxed_1473_, v_a_1471_);
lean_dec(v_size_1469_);
return v_res_1474_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmptyWithCapacity___lam__0(mut v_size_1475_: *mut lean_object, mut v_seed_1476_: u64, mut v_todo_1477_: *mut lean_object) -> *mut lean_object{
let mut v___x_1479_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1481_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1482_: u8 = 0; let mut v___x_1483_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1485_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1486_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1487_: u8 = 0; let mut v_unused_1488_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1491_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1492_: u8 = 0; let mut v___x_1494_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1495_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1496_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1479_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyWithCapacity_spec__0___redArg(v_size_1475_, v_seed_1476_, v_todo_1477_);
if lean_obj_tag(v___x_1479_) == 0 {
let mut v___x_1481_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1482_: u8 = 0; let mut v_isSharedCheck_1487_: u8 = 0; 
v_isSharedCheck_1487_ = (!lean_is_exclusive(v___x_1479_)) as u8;
if v_isSharedCheck_1487_ == 0 {
let mut v_unused_1488_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1488_ = lean_ctor_get(v___x_1479_, 0);
lean_dec(v_unused_1488_);
v___x_1481_ = v___x_1479_;
v_isShared_1482_ = v_isSharedCheck_1487_;
state = 1; continue;
} else {
lean_dec(v___x_1479_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1487_;
state = 1; continue;
}
} else {
let mut v_a_1489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1491_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1492_: u8 = 0; let mut v_isSharedCheck_1496_: u8 = 0; 
v_a_1489_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1496_ = (!lean_is_exclusive(v___x_1479_)) as u8;
if v_isSharedCheck_1496_ == 0 {
v___x_1491_ = v___x_1479_;
v_isShared_1492_ = v_isSharedCheck_1496_;
state = 3; continue;
} else {
lean_inc(v_a_1489_);
lean_dec(v___x_1479_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
state = 3; continue;
}
}
}
1 => {
v___x_1483_ = lean_box(0);
if v_isShared_1482_ == 0 {
lean_ctor_set(v___x_1481_, 0, v___x_1483_);
v___x_1485_ = v___x_1481_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1486_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
state = 2; continue;
}
}
3 => {
if v_isShared_1492_ == 0 {
v___x_1494_ = v___x_1491_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1495_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmptyWithCapacity___lam__0___boxed(mut v_size_1497_: *mut lean_object, mut v_seed_1498_: *mut lean_object, mut v_todo_1499_: *mut lean_object, mut v___y_1500_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1501_: u64 = 0; let mut v_res_1502_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1501_ = lean_unbox_uint64(v_seed_1498_);
lean_dec_ref(v_seed_1498_);
v_res_1502_ = l_benchInsertMissEmptyWithCapacity___lam__0(v_size_1497_, v_seed_boxed_1501_, v_todo_1499_);
lean_dec(v_size_1497_);
return v_res_1502_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmptyWithCapacity(mut v_seed_1503_: u64, mut v_size_1504_: *mut lean_object) -> *mut lean_object{
let mut v___x_1506_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1507_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1508_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1510_: *mut lean_object = core::ptr::null_mut(); 
v___x_1506_ = lean_unsigned_to_nat(100);
v_todo_1507_ = lean_nat_mul(v_size_1504_, v___x_1506_);
v___x_1508_ = lean_box_uint64(v_seed_1503_);
lean_inc(v_todo_1507_);
v___f_1509_ = lean_alloc_closure(l_benchInsertMissEmptyWithCapacity___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_1509_, 0, v_size_1504_);
lean_closure_set(v___f_1509_, 1, v___x_1508_);
lean_closure_set(v___f_1509_, 2, v_todo_1507_);
v___x_1510_ = l_timeNanos(v_todo_1507_, v___f_1509_);
return v___x_1510_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmptyWithCapacity___boxed(mut v_seed_1511_: *mut lean_object, mut v_size_1512_: *mut lean_object, mut v_a_1513_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1514_: u64 = 0; let mut v_res_1515_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1514_ = lean_unbox_uint64(v_seed_1511_);
lean_dec_ref(v_seed_1511_);
v_res_1515_ = l_benchInsertMissEmptyWithCapacity(v_seed_boxed_1514_, v_size_1512_);
return v_res_1515_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyWithCapacity_spec__0(mut v_size_1516_: *mut lean_object, mut v_seed_1517_: u64, mut v_inst_1518_: *mut lean_object, mut v_a_1519_: *mut lean_object) -> *mut lean_object{
let mut v___x_1521_: *mut lean_object = core::ptr::null_mut(); 
v___x_1521_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyWithCapacity_spec__0___redArg(v_size_1516_, v_seed_1517_, v_a_1519_);
return v___x_1521_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyWithCapacity_spec__0___boxed(mut v_size_1522_: *mut lean_object, mut v_seed_1523_: *mut lean_object, mut v_inst_1524_: *mut lean_object, mut v_a_1525_: *mut lean_object, mut v___y_1526_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1527_: u64 = 0; let mut v_res_1528_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1527_ = lean_unbox_uint64(v_seed_1523_);
lean_dec_ref(v_seed_1523_);
v_res_1528_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyWithCapacity_spec__0(v_size_1522_, v_seed_boxed_1527_, v_inst_1524_, v_a_1525_);
lean_dec(v_size_1522_);
return v_res_1528_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(mut v_a_1529_: u64, mut v_x_1530_: *mut lean_object) -> *mut lean_object{
let mut v_key_1531_: *mut lean_object = core::ptr::null_mut(); let mut v_value_1532_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_1533_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1535_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1536_: u8 = 0; let mut v___x_1537_: u64 = 0; let mut v___x_1538_: u8 = 0; let mut v___x_1539_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1541_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1542_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1543_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_1530_) == 0 {
return v_x_1530_;
} else {
let mut v_key_1531_: *mut lean_object = core::ptr::null_mut(); let mut v_value_1532_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_1533_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1535_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1536_: u8 = 0; let mut v_isSharedCheck_1543_: u8 = 0; 
v_key_1531_ = lean_ctor_get(v_x_1530_, 0);
v_value_1532_ = lean_ctor_get(v_x_1530_, 1);
v_tail_1533_ = lean_ctor_get(v_x_1530_, 2);
v_isSharedCheck_1543_ = (!lean_is_exclusive(v_x_1530_)) as u8;
if v_isSharedCheck_1543_ == 0 {
v___x_1535_ = v_x_1530_;
v_isShared_1536_ = v_isSharedCheck_1543_;
state = 1; continue;
} else {
lean_inc(v_tail_1533_);
lean_inc(v_value_1532_);
lean_inc(v_key_1531_);
lean_dec(v_x_1530_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1543_;
state = 1; continue;
}
}
}
1 => {
v___x_1537_ = lean_unbox_uint64(v_key_1531_);
v___x_1538_ = lean_uint64_dec_eq(v___x_1537_, v_a_1529_);
if v___x_1538_ == 0 {
let mut v___x_1539_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1541_: *mut lean_object = core::ptr::null_mut(); 
v___x_1539_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(v_a_1529_, v_tail_1533_);
if v_isShared_1536_ == 0 {
lean_ctor_set(v___x_1535_, 2, v___x_1539_);
v___x_1541_ = v___x_1535_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1542_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_key_1531_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_value_1532_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
state = 2; continue;
}
} else {
lean_del_object(v___x_1535_);
lean_dec(v_value_1532_);
lean_dec(v_key_1531_);
return v_tail_1533_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0___redArg___boxed(mut v_a_1544_: *mut lean_object, mut v_x_1545_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_1546_: u64 = 0; let mut v_res_1547_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_1546_ = lean_unbox_uint64(v_a_1544_);
lean_dec_ref(v_a_1544_);
v_res_1547_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(v_a_boxed_1546_, v_x_1545_);
return v_res_1547_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0___redArg(mut v_m_1548_: *mut lean_object, mut v_a_1549_: u64) -> *mut lean_object{
let mut v_size_1550_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_1551_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1552_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1553_: u64 = 0; let mut v___x_1554_: u64 = 0; let mut v_fold_1555_: u64 = 0; let mut v___x_1556_: u64 = 0; let mut v___x_1557_: u64 = 0; let mut v___x_1558_: u64 = 0; let mut v___x_1559_: usize = 0; let mut v___x_1560_: usize = 0; let mut v___x_1561_: usize = 0; let mut v___x_1562_: usize = 0; let mut v___x_1563_: usize = 0; let mut v_bkt_1564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1565_: u8 = 0; let mut v___x_1567_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1568_: u8 = 0; let mut v___x_1569_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_x27_1570_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1571_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1572_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1573_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1574_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1576_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1577_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1578_: u8 = 0; let mut v_unused_1579_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_1580_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_size_1550_ = lean_ctor_get(v_m_1548_, 0);
v_buckets_1551_ = lean_ctor_get(v_m_1548_, 1);
v___x_1552_ = lean_array_get_size(v_buckets_1551_);
v___x_1553_ = 32u64;
v___x_1554_ = lean_uint64_shift_right(v_a_1549_, v___x_1553_);
v_fold_1555_ = lean_uint64_xor(v_a_1549_, v___x_1554_);
v___x_1556_ = 16u64;
v___x_1557_ = lean_uint64_shift_right(v_fold_1555_, v___x_1556_);
v___x_1558_ = lean_uint64_xor(v_fold_1555_, v___x_1557_);
v___x_1559_ = lean_uint64_to_usize(v___x_1558_);
v___x_1560_ = lean_usize_of_nat(v___x_1552_);
v___x_1561_ = 1usize;
v___x_1562_ = lean_usize_sub(v___x_1560_, v___x_1561_);
v___x_1563_ = lean_usize_land(v___x_1559_, v___x_1562_);
v_bkt_1564_ = lean_array_uget_borrowed(v_buckets_1551_, v___x_1563_);
v___x_1565_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_a_1549_, v_bkt_1564_);
if v___x_1565_ == 0 {
return v_m_1548_;
} else {
let mut v___x_1567_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1568_: u8 = 0; let mut v_isSharedCheck_1578_: u8 = 0; 
lean_inc(v_bkt_1564_);
lean_inc_ref(v_buckets_1551_);
lean_inc(v_size_1550_);
v_isSharedCheck_1578_ = (!lean_is_exclusive(v_m_1548_)) as u8;
if v_isSharedCheck_1578_ == 0 {
let mut v_unused_1579_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_1580_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1579_ = lean_ctor_get(v_m_1548_, 1);
lean_dec(v_unused_1579_);
v_unused_1580_ = lean_ctor_get(v_m_1548_, 0);
lean_dec(v_unused_1580_);
v___x_1567_ = v_m_1548_;
v_isShared_1568_ = v_isSharedCheck_1578_;
state = 1; continue;
} else {
lean_dec(v_m_1548_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1578_;
state = 1; continue;
}
}
}
1 => {
v___x_1569_ = lean_box(0);
v_buckets_x27_1570_ = lean_array_uset(v_buckets_1551_, v___x_1563_, v___x_1569_);
v___x_1571_ = lean_unsigned_to_nat(1);
v___x_1572_ = lean_nat_sub(v_size_1550_, v___x_1571_);
lean_dec(v_size_1550_);
v___x_1573_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(v_a_1549_, v_bkt_1564_);
v___x_1574_ = lean_array_uset(v_buckets_x27_1570_, v___x_1563_, v___x_1573_);
if v_isShared_1568_ == 0 {
lean_ctor_set(v___x_1567_, 1, v___x_1574_);
lean_ctor_set(v___x_1567_, 0, v___x_1572_);
v___x_1576_ = v___x_1567_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1577_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0___redArg___boxed(mut v_m_1581_: *mut lean_object, mut v_a_1582_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_1583_: u64 = 0; let mut v_res_1584_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_1583_ = lean_unbox_uint64(v_a_1582_);
lean_dec_ref(v_a_1582_);
v_res_1584_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0___redArg(v_m_1581_, v_a_boxed_1583_);
return v_res_1584_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(mut v_size_1585_: *mut lean_object, mut v_a_1586_: *mut lean_object, mut v_b_1587_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_1589_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_1590_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1592_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1593_: u8 = 0; let mut v_it_1595_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1597_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1599_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1600_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1601_: u8 = 0; let mut v_memoizedLeft_1602_: *mut lean_object = core::ptr::null_mut(); let mut v_left_1603_: *mut lean_object = core::ptr::null_mut(); let mut v_right_1604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1606_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1607_: u8 = 0; let mut v___x_1608_: u64 = 0; let mut v___x_1609_: u64 = 0; let mut v___x_1610_: u64 = 0; let mut v___x_1611_: u64 = 0; let mut v___x_1612_: u64 = 0; let mut v___x_1613_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1614_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1616_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1617_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1618_: u8 = 0; let mut v_unused_1619_: *mut lean_object = core::ptr::null_mut(); let mut v_right_1620_: *mut lean_object = core::ptr::null_mut(); let mut v_left_1621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1623_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1624_: u8 = 0; let mut v_val_1625_: *mut lean_object = core::ptr::null_mut(); let mut v_remaining_1626_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_1627_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1629_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1630_: u8 = 0; let mut v___x_1631_: u64 = 0; let mut v___x_1632_: u64 = 0; let mut v___x_1633_: u64 = 0; let mut v___x_1634_: u64 = 0; let mut v___x_1635_: u64 = 0; let mut v_zero_1636_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_1637_: u8 = 0; let mut v___x_1639_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1640_: u8 = 0; let mut v___x_1641_: u64 = 0; let mut v___x_1642_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1643_: u64 = 0; let mut v___x_1644_: *mut lean_object = core::ptr::null_mut(); let mut v_size_1645_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1646_: u8 = 0; let mut v___x_1647_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1649_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1650_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1651_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1659_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1661_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1662_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1663_: u8 = 0; let mut v_unused_1664_: *mut lean_object = core::ptr::null_mut(); let mut v_n_1665_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1666_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1668_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1670_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1671_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1672_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1673_: u8 = 0; let mut v_isSharedCheck_1674_: u8 = 0; let mut v_unused_1675_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1676_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1677_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_1589_ = lean_ctor_get(v_a_1586_, 0);
v_inner_1590_ = lean_ctor_get(v_a_1586_, 1);
v_isSharedCheck_1677_ = (!lean_is_exclusive(v_a_1586_)) as u8;
if v_isSharedCheck_1677_ == 0 {
v___x_1592_ = v_a_1586_;
v_isShared_1593_ = v_isSharedCheck_1677_;
state = 1; continue;
} else {
lean_inc(v_inner_1590_);
lean_inc(v_countdown_1589_);
lean_dec(v_a_1586_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1677_;
state = 1; continue;
}
}
1 => {
v___x_1600_ = lean_unsigned_to_nat(1);
v___x_1601_ = lean_nat_dec_eq(v_countdown_1589_, v___x_1600_);
if v___x_1601_ == 0 {
let mut v_memoizedLeft_1602_: *mut lean_object = core::ptr::null_mut(); 
v_memoizedLeft_1602_ = lean_ctor_get(v_inner_1590_, 1);
lean_inc(v_memoizedLeft_1602_);
if lean_obj_tag(v_memoizedLeft_1602_) == 0 {
let mut v_left_1603_: *mut lean_object = core::ptr::null_mut(); let mut v_right_1604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1606_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1607_: u8 = 0; let mut v_isSharedCheck_1618_: u8 = 0; 
v_left_1603_ = lean_ctor_get(v_inner_1590_, 0);
v_right_1604_ = lean_ctor_get(v_inner_1590_, 2);
v_isSharedCheck_1618_ = (!lean_is_exclusive(v_inner_1590_)) as u8;
if v_isSharedCheck_1618_ == 0 {
let mut v_unused_1619_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1619_ = lean_ctor_get(v_inner_1590_, 1);
lean_dec(v_unused_1619_);
v___x_1606_ = v_inner_1590_;
v_isShared_1607_ = v_isSharedCheck_1618_;
state = 4; continue;
} else {
lean_inc(v_right_1604_);
lean_inc(v_left_1603_);
lean_dec(v_inner_1590_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1618_;
state = 4; continue;
}
} else {
let mut v_right_1620_: *mut lean_object = core::ptr::null_mut(); let mut v_left_1621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1623_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1624_: u8 = 0; let mut v_isSharedCheck_1674_: u8 = 0; 
v_right_1620_ = lean_ctor_get(v_inner_1590_, 2);
v_left_1621_ = lean_ctor_get(v_inner_1590_, 0);
v_isSharedCheck_1674_ = (!lean_is_exclusive(v_inner_1590_)) as u8;
if v_isSharedCheck_1674_ == 0 {
let mut v_unused_1675_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1675_ = lean_ctor_get(v_inner_1590_, 1);
lean_dec(v_unused_1675_);
v___x_1623_ = v_inner_1590_;
v_isShared_1624_ = v_isSharedCheck_1674_;
state = 6; continue;
} else {
lean_inc(v_right_1620_);
lean_inc(v_left_1621_);
lean_dec(v_inner_1590_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1674_;
state = 6; continue;
}
}
} else {
let mut v___x_1676_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_1592_);
lean_dec(v_inner_1590_);
lean_dec(v_countdown_1589_);
v___x_1676_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1676_, 0, v_b_1587_);
return v___x_1676_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg___boxed(mut v_size_1678_: *mut lean_object, mut v_a_1679_: *mut lean_object, mut v_b_1680_: *mut lean_object, mut v___y_1681_: *mut lean_object) -> *mut lean_object{
let mut v_res_1682_: *mut lean_object = core::ptr::null_mut(); 
v_res_1682_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(v_size_1678_, v_a_1679_, v_b_1680_);
lean_dec(v_size_1678_);
return v_res_1682_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2_spec__3___redArg(mut v_eraseIter_1683_: u64, mut v_newIter_1684_: *mut lean_object, mut v_size_1685_: *mut lean_object, mut v_a_1686_: *mut lean_object) -> *mut lean_object{
let mut v_fst_1688_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1692_: u8 = 0; let mut v___x_1693_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1694_: u8 = 0; let mut v___x_1695_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1696_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1697_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1698_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1699_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1700_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1701_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1702_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1703_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1705_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1707_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1708_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1710_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1711_: u8 = 0; let mut v___x_1713_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1714_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1715_: u8 = 0; let mut v___x_1717_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1718_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1719_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1720_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_1688_ = lean_ctor_get(v_a_1686_, 0);
v_snd_1689_ = lean_ctor_get(v_a_1686_, 1);
v_isSharedCheck_1720_ = (!lean_is_exclusive(v_a_1686_)) as u8;
if v_isSharedCheck_1720_ == 0 {
v___x_1691_ = v_a_1686_;
v_isShared_1692_ = v_isSharedCheck_1720_;
state = 1; continue;
} else {
lean_inc(v_snd_1689_);
lean_inc(v_fst_1688_);
lean_dec(v_a_1686_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1720_;
state = 1; continue;
}
}
1 => {
v___x_1693_ = lean_unsigned_to_nat(0);
v___x_1694_ = lean_nat_dec_eq(v_snd_1689_, v___x_1693_);
if v___x_1694_ == 0 {
let mut v___x_1695_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1696_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1697_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1698_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1699_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1700_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1701_: *mut lean_object = core::ptr::null_mut(); 
v___x_1695_ = lean_box(0);
v___x_1696_ = lean_box_uint64(v_eraseIter_1683_);
lean_inc_ref(v_newIter_1684_);
v___x_1697_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___x_1695_);
lean_ctor_set(v___x_1697_, 2, v_newIter_1684_);
v___x_1698_ = lean_unsigned_to_nat(1);
v___x_1699_ = lean_nat_add(v_size_1685_, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
lean_ctor_set(v___x_1700_, 1, v___x_1697_);
v___x_1701_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(v_size_1685_, v___x_1700_, v_fst_1688_);
if lean_obj_tag(v___x_1701_) == 0 {
let mut v_a_1702_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1703_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1705_: *mut lean_object = core::ptr::null_mut(); 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = lean_nat_sub(v_snd_1689_, v_size_1685_);
lean_dec(v_snd_1689_);
if v_isShared_1692_ == 0 {
lean_ctor_set(v___x_1691_, 1, v___x_1703_);
lean_ctor_set(v___x_1691_, 0, v_a_1702_);
v___x_1705_ = v___x_1691_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1707_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1702_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1707_;
state = 2; continue;
}
} else {
let mut v_a_1708_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1710_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1711_: u8 = 0; let mut v_isSharedCheck_1715_: u8 = 0; 
lean_del_object(v___x_1691_);
lean_dec(v_snd_1689_);
lean_dec_ref(v_newIter_1684_);
v_a_1708_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1715_ = (!lean_is_exclusive(v___x_1701_)) as u8;
if v_isSharedCheck_1715_ == 0 {
v___x_1710_ = v___x_1701_;
v_isShared_1711_ = v_isSharedCheck_1715_;
state = 3; continue;
} else {
lean_inc(v_a_1708_);
lean_dec(v___x_1701_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
state = 3; continue;
}
}
} else {
let mut v___x_1717_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_newIter_1684_);
if v_isShared_1692_ == 0 {
v___x_1717_ = v___x_1691_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_1719_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_fst_1688_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_snd_1689_);
v___x_1717_ = v_reuseFailAlloc_1719_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2_spec__3___redArg___boxed(mut v_eraseIter_1721_: *mut lean_object, mut v_newIter_1722_: *mut lean_object, mut v_size_1723_: *mut lean_object, mut v_a_1724_: *mut lean_object, mut v___y_1725_: *mut lean_object) -> *mut lean_object{
let mut v_eraseIter_boxed_1726_: u64 = 0; let mut v_res_1727_: *mut lean_object = core::ptr::null_mut(); 
v_eraseIter_boxed_1726_ = lean_unbox_uint64(v_eraseIter_1721_);
lean_dec_ref(v_eraseIter_1721_);
v_res_1727_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2_spec__3___redArg(v_eraseIter_boxed_1726_, v_newIter_1722_, v_size_1723_, v_a_1724_);
lean_dec(v_size_1723_);
return v_res_1727_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg(mut v_size_1728_: *mut lean_object, mut v_eraseIter_1729_: u64, mut v_newIter_1730_: *mut lean_object, mut v_a_1731_: *mut lean_object) -> *mut lean_object{
let mut v_fst_1733_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1734_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1736_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1737_: u8 = 0; let mut v___x_1738_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1739_: u8 = 0; let mut v___x_1740_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1741_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1742_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1743_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1744_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1745_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1746_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1747_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1748_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1750_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1751_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1752_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1753_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1755_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1756_: u8 = 0; let mut v___x_1758_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1759_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1760_: u8 = 0; let mut v___x_1762_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1763_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1764_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1765_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_1733_ = lean_ctor_get(v_a_1731_, 0);
v_snd_1734_ = lean_ctor_get(v_a_1731_, 1);
v_isSharedCheck_1765_ = (!lean_is_exclusive(v_a_1731_)) as u8;
if v_isSharedCheck_1765_ == 0 {
v___x_1736_ = v_a_1731_;
v_isShared_1737_ = v_isSharedCheck_1765_;
state = 1; continue;
} else {
lean_inc(v_snd_1734_);
lean_inc(v_fst_1733_);
lean_dec(v_a_1731_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1765_;
state = 1; continue;
}
}
1 => {
v___x_1738_ = lean_unsigned_to_nat(0);
v___x_1739_ = lean_nat_dec_eq(v_snd_1734_, v___x_1738_);
if v___x_1739_ == 0 {
let mut v___x_1740_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1741_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1742_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1743_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1744_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1745_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1746_: *mut lean_object = core::ptr::null_mut(); 
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_box_uint64(v_eraseIter_1729_);
lean_inc_ref(v_newIter_1730_);
v___x_1742_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v___x_1740_);
lean_ctor_set(v___x_1742_, 2, v_newIter_1730_);
v___x_1743_ = lean_unsigned_to_nat(1);
v___x_1744_ = lean_nat_add(v_size_1728_, v___x_1743_);
v___x_1745_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___x_1742_);
v___x_1746_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(v_size_1728_, v___x_1745_, v_fst_1733_);
if lean_obj_tag(v___x_1746_) == 0 {
let mut v_a_1747_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1748_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1750_: *mut lean_object = core::ptr::null_mut(); 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = lean_nat_sub(v_snd_1734_, v_size_1728_);
lean_dec(v_snd_1734_);
if v_isShared_1737_ == 0 {
lean_ctor_set(v___x_1736_, 1, v___x_1748_);
lean_ctor_set(v___x_1736_, 0, v_a_1747_);
v___x_1750_ = v___x_1736_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1752_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1747_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1752_;
state = 2; continue;
}
} else {
let mut v_a_1753_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1755_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1756_: u8 = 0; let mut v_isSharedCheck_1760_: u8 = 0; 
lean_del_object(v___x_1736_);
lean_dec(v_snd_1734_);
lean_dec_ref(v_newIter_1730_);
v_a_1753_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1760_ = (!lean_is_exclusive(v___x_1746_)) as u8;
if v_isSharedCheck_1760_ == 0 {
v___x_1755_ = v___x_1746_;
v_isShared_1756_ = v_isSharedCheck_1760_;
state = 3; continue;
} else {
lean_inc(v_a_1753_);
lean_dec(v___x_1746_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
state = 3; continue;
}
}
} else {
let mut v___x_1762_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_newIter_1730_);
if v_isShared_1737_ == 0 {
v___x_1762_ = v___x_1736_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_1764_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_fst_1733_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_snd_1734_);
v___x_1762_ = v_reuseFailAlloc_1764_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg___boxed(mut v_size_1766_: *mut lean_object, mut v_eraseIter_1767_: *mut lean_object, mut v_newIter_1768_: *mut lean_object, mut v_a_1769_: *mut lean_object, mut v___y_1770_: *mut lean_object) -> *mut lean_object{
let mut v_eraseIter_boxed_1771_: u64 = 0; let mut v_res_1772_: *mut lean_object = core::ptr::null_mut(); 
v_eraseIter_boxed_1771_ = lean_unbox_uint64(v_eraseIter_1767_);
lean_dec_ref(v_eraseIter_1767_);
v_res_1772_ = l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg(v_size_1766_, v_eraseIter_boxed_1771_, v_newIter_1768_, v_a_1769_);
lean_dec(v_size_1766_);
return v_res_1772_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchEraseInsert___lam__0(mut v_size_1773_: *mut lean_object, mut v_seed_1774_: u64, mut v_newIter_1775_: *mut lean_object, mut v___x_1776_: *mut lean_object) -> *mut lean_object{
let mut v___x_1778_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1780_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1781_: u8 = 0; let mut v___x_1782_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1784_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1785_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1786_: u8 = 0; let mut v_unused_1787_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1790_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1791_: u8 = 0; let mut v___x_1793_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1794_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1795_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1778_ = l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg(v_size_1773_, v_seed_1774_, v_newIter_1775_, v___x_1776_);
if lean_obj_tag(v___x_1778_) == 0 {
let mut v___x_1780_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1781_: u8 = 0; let mut v_isSharedCheck_1786_: u8 = 0; 
v_isSharedCheck_1786_ = (!lean_is_exclusive(v___x_1778_)) as u8;
if v_isSharedCheck_1786_ == 0 {
let mut v_unused_1787_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1787_ = lean_ctor_get(v___x_1778_, 0);
lean_dec(v_unused_1787_);
v___x_1780_ = v___x_1778_;
v_isShared_1781_ = v_isSharedCheck_1786_;
state = 1; continue;
} else {
lean_dec(v___x_1778_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
state = 1; continue;
}
} else {
let mut v_a_1788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1790_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1791_: u8 = 0; let mut v_isSharedCheck_1795_: u8 = 0; 
v_a_1788_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1795_ = (!lean_is_exclusive(v___x_1778_)) as u8;
if v_isSharedCheck_1795_ == 0 {
v___x_1790_ = v___x_1778_;
v_isShared_1791_ = v_isSharedCheck_1795_;
state = 3; continue;
} else {
lean_inc(v_a_1788_);
lean_dec(v___x_1778_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
state = 3; continue;
}
}
}
1 => {
v___x_1782_ = lean_box(0);
if v_isShared_1781_ == 0 {
lean_ctor_set(v___x_1780_, 0, v___x_1782_);
v___x_1784_ = v___x_1780_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1785_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
state = 2; continue;
}
}
3 => {
if v_isShared_1791_ == 0 {
v___x_1793_ = v___x_1790_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1794_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchEraseInsert___lam__0___boxed(mut v_size_1796_: *mut lean_object, mut v_seed_1797_: *mut lean_object, mut v_newIter_1798_: *mut lean_object, mut v___x_1799_: *mut lean_object, mut v___y_1800_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1801_: u64 = 0; let mut v_res_1802_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1801_ = lean_unbox_uint64(v_seed_1797_);
lean_dec_ref(v_seed_1797_);
v_res_1802_ = l_benchEraseInsert___lam__0(v_size_1796_, v_seed_boxed_1801_, v_newIter_1798_, v___x_1799_);
lean_dec(v_size_1796_);
return v_res_1802_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchEraseInsert(mut v_seed_1803_: u64, mut v_size_1804_: *mut lean_object) -> *mut lean_object{
let mut v_map_1806_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1807_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1808_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1809_: *mut lean_object = core::ptr::null_mut(); let mut v_newIter_1810_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1811_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1812_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1813_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1814_: *mut lean_object = core::ptr::null_mut(); 
v_map_1806_ = l_mkMapWithCap(v_seed_1803_, v_size_1804_);
v___x_1807_ = lean_unsigned_to_nat(100);
v_todo_1808_ = lean_nat_mul(v_size_1804_, v___x_1807_);
v___x_1809_ = lean_box_uint64(v_seed_1803_);
lean_inc(v_size_1804_);
v_newIter_1810_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_newIter_1810_, 0, v_size_1804_);
lean_ctor_set(v_newIter_1810_, 1, v___x_1809_);
lean_inc(v_todo_1808_);
v___x_1811_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1811_, 0, v_map_1806_);
lean_ctor_set(v___x_1811_, 1, v_todo_1808_);
v___x_1812_ = lean_box_uint64(v_seed_1803_);
v___f_1813_ = lean_alloc_closure(l_benchEraseInsert___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
lean_closure_set(v___f_1813_, 0, v_size_1804_);
lean_closure_set(v___f_1813_, 1, v___x_1812_);
lean_closure_set(v___f_1813_, 2, v_newIter_1810_);
lean_closure_set(v___f_1813_, 3, v___x_1811_);
v___x_1814_ = l_timeNanos(v_todo_1808_, v___f_1813_);
return v___x_1814_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchEraseInsert___boxed(mut v_seed_1815_: *mut lean_object, mut v_size_1816_: *mut lean_object, mut v_a_1817_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1818_: u64 = 0; let mut v_res_1819_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1818_ = lean_unbox_uint64(v_seed_1815_);
lean_dec_ref(v_seed_1815_);
v_res_1819_ = l_benchEraseInsert(v_seed_boxed_1818_, v_size_1816_);
return v_res_1819_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0(mut v_00_u03b2_1820_: *mut lean_object, mut v_m_1821_: *mut lean_object, mut v_a_1822_: u64) -> *mut lean_object{
let mut v___x_1823_: *mut lean_object = core::ptr::null_mut(); 
v___x_1823_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0___redArg(v_m_1821_, v_a_1822_);
return v___x_1823_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0___boxed(mut v_00_u03b2_1824_: *mut lean_object, mut v_m_1825_: *mut lean_object, mut v_a_1826_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_1827_: u64 = 0; let mut v_res_1828_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_1827_ = lean_unbox_uint64(v_a_1826_);
lean_dec_ref(v_a_1826_);
v_res_1828_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0(v_00_u03b2_1824_, v_m_1825_, v_a_boxed_1827_);
return v_res_1828_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1(mut v_size_1829_: *mut lean_object, mut v_inst_1830_: *mut lean_object, mut v_R_1831_: *mut lean_object, mut v_a_1832_: *mut lean_object, mut v_b_1833_: *mut lean_object, mut v_c_1834_: *mut lean_object) -> *mut lean_object{
let mut v___x_1836_: *mut lean_object = core::ptr::null_mut(); 
v___x_1836_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(v_size_1829_, v_a_1832_, v_b_1833_);
return v___x_1836_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___boxed(mut v_size_1837_: *mut lean_object, mut v_inst_1838_: *mut lean_object, mut v_R_1839_: *mut lean_object, mut v_a_1840_: *mut lean_object, mut v_b_1841_: *mut lean_object, mut v_c_1842_: *mut lean_object, mut v___y_1843_: *mut lean_object) -> *mut lean_object{
let mut v_res_1844_: *mut lean_object = core::ptr::null_mut(); 
v_res_1844_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1(v_size_1837_, v_inst_1838_, v_R_1839_, v_a_1840_, v_b_1841_, v_c_1842_);
lean_dec(v_size_1837_);
return v_res_1844_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2(mut v_size_1845_: *mut lean_object, mut v_eraseIter_1846_: u64, mut v_newIter_1847_: *mut lean_object, mut v_inst_1848_: *mut lean_object, mut v_a_1849_: *mut lean_object) -> *mut lean_object{
let mut v___x_1851_: *mut lean_object = core::ptr::null_mut(); 
v___x_1851_ = l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg(v_size_1845_, v_eraseIter_1846_, v_newIter_1847_, v_a_1849_);
return v___x_1851_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___boxed(mut v_size_1852_: *mut lean_object, mut v_eraseIter_1853_: *mut lean_object, mut v_newIter_1854_: *mut lean_object, mut v_inst_1855_: *mut lean_object, mut v_a_1856_: *mut lean_object, mut v___y_1857_: *mut lean_object) -> *mut lean_object{
let mut v_eraseIter_boxed_1858_: u64 = 0; let mut v_res_1859_: *mut lean_object = core::ptr::null_mut(); 
v_eraseIter_boxed_1858_ = lean_unbox_uint64(v_eraseIter_1853_);
lean_dec_ref(v_eraseIter_1853_);
v_res_1859_ = l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2(v_size_1852_, v_eraseIter_boxed_1858_, v_newIter_1854_, v_inst_1855_, v_a_1856_);
lean_dec(v_size_1852_);
return v_res_1859_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0(mut v_00_u03b2_1860_: *mut lean_object, mut v_a_1861_: u64, mut v_x_1862_: *mut lean_object) -> *mut lean_object{
let mut v___x_1863_: *mut lean_object = core::ptr::null_mut(); 
v___x_1863_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(v_a_1861_, v_x_1862_);
return v___x_1863_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0___boxed(mut v_00_u03b2_1864_: *mut lean_object, mut v_a_1865_: *mut lean_object, mut v_x_1866_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_1867_: u64 = 0; let mut v_res_1868_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_1867_ = lean_unbox_uint64(v_a_1865_);
lean_dec_ref(v_a_1865_);
v_res_1868_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00benchEraseInsert_spec__0_spec__0(v_00_u03b2_1864_, v_a_boxed_1867_, v_x_1866_);
return v_res_1868_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2_spec__3(mut v_eraseIter_1869_: u64, mut v_newIter_1870_: *mut lean_object, mut v_size_1871_: *mut lean_object, mut v_inst_1872_: *mut lean_object, mut v_a_1873_: *mut lean_object) -> *mut lean_object{
let mut v___x_1875_: *mut lean_object = core::ptr::null_mut(); 
v___x_1875_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2_spec__3___redArg(v_eraseIter_1869_, v_newIter_1870_, v_size_1871_, v_a_1873_);
return v___x_1875_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2_spec__3___boxed(mut v_eraseIter_1876_: *mut lean_object, mut v_newIter_1877_: *mut lean_object, mut v_size_1878_: *mut lean_object, mut v_inst_1879_: *mut lean_object, mut v_a_1880_: *mut lean_object, mut v___y_1881_: *mut lean_object) -> *mut lean_object{
let mut v_eraseIter_boxed_1882_: u64 = 0; let mut v_res_1883_: *mut lean_object = core::ptr::null_mut(); 
v_eraseIter_boxed_1882_ = lean_unbox_uint64(v_eraseIter_1876_);
lean_dec_ref(v_eraseIter_1876_);
v_res_1883_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2_spec__3(v_eraseIter_boxed_1882_, v_newIter_1877_, v_size_1878_, v_inst_1879_, v_a_1880_);
lean_dec(v_size_1878_);
return v_res_1883_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_testPrimes() -> *mut lean_object{
let mut v___x_1884_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1885_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1886_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1887_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1888_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1889_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1890_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1891_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1892_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1893_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1894_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1895_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1896_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1897_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1898_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1899_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1900_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1901_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1902_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1903_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1904_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1905_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1906_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1907_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1908_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1909_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1910_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1911_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1912_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1913_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1914_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1915_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1916_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1917_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1918_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1919_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1920_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1921_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1922_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1923_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1924_: *mut lean_object = core::ptr::null_mut(); 
v___x_1884_ = lean_unsigned_to_nat(2);
v___x_1885_ = lean_unsigned_to_nat(3);
v___x_1886_ = lean_unsigned_to_nat(5);
v___x_1887_ = lean_unsigned_to_nat(7);
v___x_1888_ = lean_unsigned_to_nat(11);
v___x_1889_ = lean_unsigned_to_nat(13);
v___x_1890_ = lean_unsigned_to_nat(17);
v___x_1891_ = lean_unsigned_to_nat(19);
v___x_1892_ = lean_unsigned_to_nat(23);
v___x_1893_ = lean_unsigned_to_nat(29);
v___x_1894_ = lean_unsigned_to_nat(31);
v___x_1895_ = lean_unsigned_to_nat(37);
v___x_1896_ = lean_unsigned_to_nat(41);
v___x_1897_ = lean_unsigned_to_nat(43);
v___x_1898_ = lean_unsigned_to_nat(47);
v___x_1899_ = lean_unsigned_to_nat(53);
v___x_1900_ = lean_unsigned_to_nat(59);
v___x_1901_ = lean_unsigned_to_nat(61);
v___x_1902_ = lean_unsigned_to_nat(67);
v___x_1903_ = lean_unsigned_to_nat(71);
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1906_, 0, v___x_1902_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1907_, 0, v___x_1901_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1908_, 0, v___x_1900_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1909_, 0, v___x_1899_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1910_, 0, v___x_1898_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1911_, 0, v___x_1897_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1912_, 0, v___x_1896_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1913_, 0, v___x_1895_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1914_, 0, v___x_1894_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1915_, 0, v___x_1893_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1916_, 0, v___x_1892_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1917_, 0, v___x_1891_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1918_, 0, v___x_1890_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1919_, 0, v___x_1889_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1920_, 0, v___x_1888_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1921_, 0, v___x_1887_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1922_, 0, v___x_1886_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1923_, 0, v___x_1885_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_1924_, 0, v___x_1884_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
return v___x_1924_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_getfirst___redArg(mut v_l_1925_: *mut lean_object, mut v_n_1926_: *mut lean_object) -> *mut lean_object{
let mut v_zero_1927_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_1928_: u8 = 0; let mut v___x_1929_: *mut lean_object = core::ptr::null_mut(); let mut v_head_1930_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_1931_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1933_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1934_: u8 = 0; let mut v_one_1935_: *mut lean_object = core::ptr::null_mut(); let mut v_n_1936_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1937_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1939_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1940_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1941_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_zero_1927_ = lean_unsigned_to_nat(0);
v_isZero_1928_ = lean_nat_dec_eq(v_n_1926_, v_zero_1927_);
if v_isZero_1928_ == 1 {
let mut v___x_1929_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_l_1925_);
v___x_1929_ = lean_box(0);
return v___x_1929_;
} else {
if lean_obj_tag(v_l_1925_) == 0 {
return v_l_1925_;
} else {
let mut v_head_1930_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_1931_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1933_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1934_: u8 = 0; let mut v_isSharedCheck_1941_: u8 = 0; 
v_head_1930_ = lean_ctor_get(v_l_1925_, 0);
v_tail_1931_ = lean_ctor_get(v_l_1925_, 1);
v_isSharedCheck_1941_ = (!lean_is_exclusive(v_l_1925_)) as u8;
if v_isSharedCheck_1941_ == 0 {
v___x_1933_ = v_l_1925_;
v_isShared_1934_ = v_isSharedCheck_1941_;
state = 1; continue;
} else {
lean_inc(v_tail_1931_);
lean_inc(v_head_1930_);
lean_dec(v_l_1925_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1941_;
state = 1; continue;
}
}
}
}
1 => {
v_one_1935_ = lean_unsigned_to_nat(1);
v_n_1936_ = lean_nat_sub(v_n_1926_, v_one_1935_);
v___x_1937_ = l_List_getfirst___redArg(v_tail_1931_, v_n_1936_);
lean_dec(v_n_1936_);
if v_isShared_1934_ == 0 {
lean_ctor_set(v___x_1933_, 1, v___x_1937_);
v___x_1939_ = v___x_1933_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1940_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_head_1930_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_getfirst___redArg___boxed(mut v_l_1942_: *mut lean_object, mut v_n_1943_: *mut lean_object) -> *mut lean_object{
let mut v_res_1944_: *mut lean_object = core::ptr::null_mut(); 
v_res_1944_ = l_List_getfirst___redArg(v_l_1942_, v_n_1943_);
lean_dec(v_n_1943_);
return v_res_1944_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_getfirst(mut v_00_u03b1_1945_: *mut lean_object, mut v_l_1946_: *mut lean_object, mut v_n_1947_: *mut lean_object) -> *mut lean_object{
let mut v___x_1948_: *mut lean_object = core::ptr::null_mut(); 
v___x_1948_ = l_List_getfirst___redArg(v_l_1946_, v_n_1947_);
return v___x_1948_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_getfirst___boxed(mut v_00_u03b1_1949_: *mut lean_object, mut v_l_1950_: *mut lean_object, mut v_n_1951_: *mut lean_object) -> *mut lean_object{
let mut v_res_1952_: *mut lean_object = core::ptr::null_mut(); 
v_res_1952_ = l_List_getfirst(v_00_u03b1_1949_, v_l_1950_, v_n_1951_);
lean_dec(v_n_1951_);
return v_res_1952_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1_spec__2_spec__4___redArg(mut v_x_1953_: *mut lean_object, mut v_x_1954_: *mut lean_object) -> *mut lean_object{
let mut v_key_1955_: *mut lean_object = core::ptr::null_mut(); let mut v_value_1956_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_1957_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1959_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1960_: u8 = 0; let mut v___x_1961_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1962_: u64 = 0; let mut v___x_1963_: u64 = 0; let mut v___x_1964_: u64 = 0; let mut v_fold_1965_: u64 = 0; let mut v___x_1966_: u64 = 0; let mut v___x_1967_: u64 = 0; let mut v___x_1968_: u64 = 0; let mut v___x_1969_: usize = 0; let mut v___x_1970_: usize = 0; let mut v___x_1971_: usize = 0; let mut v___x_1972_: usize = 0; let mut v___x_1973_: usize = 0; let mut v___x_1974_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1976_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1977_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1979_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1980_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_1954_) == 0 {
return v_x_1953_;
} else {
let mut v_key_1955_: *mut lean_object = core::ptr::null_mut(); let mut v_value_1956_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_1957_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1959_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1960_: u8 = 0; let mut v_isSharedCheck_1980_: u8 = 0; 
v_key_1955_ = lean_ctor_get(v_x_1954_, 0);
v_value_1956_ = lean_ctor_get(v_x_1954_, 1);
v_tail_1957_ = lean_ctor_get(v_x_1954_, 2);
v_isSharedCheck_1980_ = (!lean_is_exclusive(v_x_1954_)) as u8;
if v_isSharedCheck_1980_ == 0 {
v___x_1959_ = v_x_1954_;
v_isShared_1960_ = v_isSharedCheck_1980_;
state = 1; continue;
} else {
lean_inc(v_tail_1957_);
lean_inc(v_value_1956_);
lean_inc(v_key_1955_);
lean_dec(v_x_1954_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1980_;
state = 1; continue;
}
}
}
1 => {
v___x_1961_ = lean_array_get_size(v_x_1953_);
v___x_1962_ = lean_uint64_of_nat(v_key_1955_);
v___x_1963_ = 32u64;
v___x_1964_ = lean_uint64_shift_right(v___x_1962_, v___x_1963_);
v_fold_1965_ = lean_uint64_xor(v___x_1962_, v___x_1964_);
v___x_1966_ = 16u64;
v___x_1967_ = lean_uint64_shift_right(v_fold_1965_, v___x_1966_);
v___x_1968_ = lean_uint64_xor(v_fold_1965_, v___x_1967_);
v___x_1969_ = lean_uint64_to_usize(v___x_1968_);
v___x_1970_ = lean_usize_of_nat(v___x_1961_);
v___x_1971_ = 1usize;
v___x_1972_ = lean_usize_sub(v___x_1970_, v___x_1971_);
v___x_1973_ = lean_usize_land(v___x_1969_, v___x_1972_);
v___x_1974_ = lean_array_uget_borrowed(v_x_1953_, v___x_1973_);
lean_inc(v___x_1974_);
if v_isShared_1960_ == 0 {
lean_ctor_set(v___x_1959_, 2, v___x_1974_);
v___x_1976_ = v___x_1959_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1979_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_key_1955_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_value_1956_);
lean_ctor_set(v_reuseFailAlloc_1979_, 2, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1979_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1_spec__2___redArg(mut v_i_1981_: *mut lean_object, mut v_source_1982_: *mut lean_object, mut v_target_1983_: *mut lean_object) -> *mut lean_object{
let mut v___x_1984_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1985_: u8 = 0; let mut v_es_1986_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1987_: *mut lean_object = core::ptr::null_mut(); let mut v_source_1988_: *mut lean_object = core::ptr::null_mut(); let mut v_target_1989_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1990_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1991_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1984_ = lean_array_get_size(v_source_1982_);
v___x_1985_ = lean_nat_dec_lt(v_i_1981_, v___x_1984_);
if v___x_1985_ == 0 {
lean_dec_ref(v_source_1982_);
lean_dec(v_i_1981_);
return v_target_1983_;
} else {
let mut v_es_1986_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1987_: *mut lean_object = core::ptr::null_mut(); let mut v_source_1988_: *mut lean_object = core::ptr::null_mut(); let mut v_target_1989_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1990_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1991_: *mut lean_object = core::ptr::null_mut(); 
v_es_1986_ = lean_array_fget(v_source_1982_, v_i_1981_);
v___x_1987_ = lean_box(0);
v_source_1988_ = lean_array_fset(v_source_1982_, v_i_1981_, v___x_1987_);
v_target_1989_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1983_, v_es_1986_);
v___x_1990_ = lean_unsigned_to_nat(1);
v___x_1991_ = lean_nat_add(v_i_1981_, v___x_1990_);
lean_dec(v_i_1981_);
v_i_1981_ = v___x_1991_;
v_source_1982_ = v_source_1988_;
v_target_1983_ = v_target_1989_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1___redArg(mut v_data_1993_: *mut lean_object) -> *mut lean_object{
let mut v___x_1994_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1995_: *mut lean_object = core::ptr::null_mut(); let mut v_nbuckets_1996_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1997_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1998_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1999_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2000_: *mut lean_object = core::ptr::null_mut(); 
v___x_1994_ = lean_array_get_size(v_data_1993_);
v___x_1995_ = lean_unsigned_to_nat(2);
v_nbuckets_1996_ = lean_nat_mul(v___x_1994_, v___x_1995_);
v___x_1997_ = lean_unsigned_to_nat(0);
v___x_1998_ = lean_box(0);
v___x_1999_ = lean_mk_array(v_nbuckets_1996_, v___x_1998_);
v___x_2000_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1_spec__2___redArg(v___x_1997_, v_data_1993_, v___x_1999_);
return v___x_2000_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__0___redArg(mut v_a_2001_: *mut lean_object, mut v_x_2002_: *mut lean_object) -> u8{
let mut v___x_2003_: u8 = 0; let mut v_key_2004_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2005_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2006_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_2002_) == 0 {
let mut v___x_2003_: u8 = 0; 
v___x_2003_ = 0;
return v___x_2003_;
} else {
let mut v_key_2004_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2005_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2006_: u8 = 0; 
v_key_2004_ = lean_ctor_get(v_x_2002_, 0);
v_tail_2005_ = lean_ctor_get(v_x_2002_, 2);
v___x_2006_ = lean_nat_dec_eq(v_key_2004_, v_a_2001_);
if v___x_2006_ == 0 {
v_x_2002_ = v_tail_2005_;
state = 0; continue;
} else {
return v___x_2006_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__0___redArg___boxed(mut v_a_2008_: *mut lean_object, mut v_x_2009_: *mut lean_object) -> *mut lean_object{
let mut v_res_2010_: u8 = 0; let mut v_r_2011_: *mut lean_object = core::ptr::null_mut(); 
v_res_2010_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__0___redArg(v_a_2008_, v_x_2009_);
lean_dec(v_x_2009_);
lean_dec(v_a_2008_);
v_r_2011_ = lean_box((v_res_2010_) as usize);
return v_r_2011_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0___redArg(mut v_m_2012_: *mut lean_object, mut v_a_2013_: *mut lean_object, mut v_b_2014_: *mut lean_object) -> *mut lean_object{
let mut v_size_2015_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_2016_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2017_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2018_: u64 = 0; let mut v___x_2019_: u64 = 0; let mut v___x_2020_: u64 = 0; let mut v_fold_2021_: u64 = 0; let mut v___x_2022_: u64 = 0; let mut v___x_2023_: u64 = 0; let mut v___x_2024_: u64 = 0; let mut v___x_2025_: usize = 0; let mut v___x_2026_: usize = 0; let mut v___x_2027_: usize = 0; let mut v___x_2028_: usize = 0; let mut v___x_2029_: usize = 0; let mut v_bkt_2030_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2031_: u8 = 0; let mut v___x_2033_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2034_: u8 = 0; let mut v___x_2035_: *mut lean_object = core::ptr::null_mut(); let mut v_size_x27_2036_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2037_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_x27_2038_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2039_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2040_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2041_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2042_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2043_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2044_: u8 = 0; let mut v_val_2045_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2047_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2048_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2050_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2051_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2052_: u8 = 0; let mut v_unused_2053_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_2054_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_size_2015_ = lean_ctor_get(v_m_2012_, 0);
v_buckets_2016_ = lean_ctor_get(v_m_2012_, 1);
v___x_2017_ = lean_array_get_size(v_buckets_2016_);
v___x_2018_ = lean_uint64_of_nat(v_a_2013_);
v___x_2019_ = 32u64;
v___x_2020_ = lean_uint64_shift_right(v___x_2018_, v___x_2019_);
v_fold_2021_ = lean_uint64_xor(v___x_2018_, v___x_2020_);
v___x_2022_ = 16u64;
v___x_2023_ = lean_uint64_shift_right(v_fold_2021_, v___x_2022_);
v___x_2024_ = lean_uint64_xor(v_fold_2021_, v___x_2023_);
v___x_2025_ = lean_uint64_to_usize(v___x_2024_);
v___x_2026_ = lean_usize_of_nat(v___x_2017_);
v___x_2027_ = 1usize;
v___x_2028_ = lean_usize_sub(v___x_2026_, v___x_2027_);
v___x_2029_ = lean_usize_land(v___x_2025_, v___x_2028_);
v_bkt_2030_ = lean_array_uget_borrowed(v_buckets_2016_, v___x_2029_);
v___x_2031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__0___redArg(v_a_2013_, v_bkt_2030_);
if v___x_2031_ == 0 {
let mut v___x_2033_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2034_: u8 = 0; let mut v_isSharedCheck_2052_: u8 = 0; 
lean_inc_ref(v_buckets_2016_);
lean_inc(v_size_2015_);
v_isSharedCheck_2052_ = (!lean_is_exclusive(v_m_2012_)) as u8;
if v_isSharedCheck_2052_ == 0 {
let mut v_unused_2053_: *mut lean_object = core::ptr::null_mut(); let mut v_unused_2054_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2053_ = lean_ctor_get(v_m_2012_, 1);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_m_2012_, 0);
lean_dec(v_unused_2054_);
v___x_2033_ = v_m_2012_;
v_isShared_2034_ = v_isSharedCheck_2052_;
state = 1; continue;
} else {
lean_dec(v_m_2012_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2052_;
state = 1; continue;
}
} else {
lean_dec(v_b_2014_);
lean_dec(v_a_2013_);
return v_m_2012_;
}
}
1 => {
v___x_2035_ = lean_unsigned_to_nat(1);
v_size_x27_2036_ = lean_nat_add(v_size_2015_, v___x_2035_);
lean_dec(v_size_2015_);
lean_inc(v_bkt_2030_);
v___x_2037_ = lean_alloc_ctor(1, 3, (0) as u32);
lean_ctor_set(v___x_2037_, 0, v_a_2013_);
lean_ctor_set(v___x_2037_, 1, v_b_2014_);
lean_ctor_set(v___x_2037_, 2, v_bkt_2030_);
v_buckets_x27_2038_ = lean_array_uset(v_buckets_2016_, v___x_2029_, v___x_2037_);
v___x_2039_ = lean_unsigned_to_nat(4);
v___x_2040_ = lean_nat_mul(v_size_x27_2036_, v___x_2039_);
v___x_2041_ = lean_unsigned_to_nat(3);
v___x_2042_ = lean_nat_div(v___x_2040_, v___x_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_array_get_size(v_buckets_x27_2038_);
v___x_2044_ = lean_nat_dec_le(v___x_2042_, v___x_2043_);
lean_dec(v___x_2042_);
if v___x_2044_ == 0 {
let mut v_val_2045_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2047_: *mut lean_object = core::ptr::null_mut(); 
v_val_2045_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1___redArg(v_buckets_x27_2038_);
if v_isShared_2034_ == 0 {
lean_ctor_set(v___x_2033_, 1, v_val_2045_);
lean_ctor_set(v___x_2033_, 0, v_size_x27_2036_);
v___x_2047_ = v___x_2033_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2048_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_size_x27_2036_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_val_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
state = 2; continue;
}
} else {
let mut v___x_2050_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_2034_ == 0 {
lean_ctor_set(v___x_2033_, 1, v_buckets_x27_2038_);
lean_ctor_set(v___x_2033_, 0, v_size_x27_2036_);
v___x_2050_ = v___x_2033_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_2051_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_size_x27_2036_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_buckets_x27_2038_);
v___x_2050_ = v_reuseFailAlloc_2051_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00createTest_spec__1___redArg(mut v_a_2055_: *mut lean_object) -> *mut lean_object{
let mut v_fst_2057_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_2058_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2060_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2061_: u8 = 0; let mut v___x_2062_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2063_: u8 = 0; let mut v___x_2065_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2066_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2067_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2068_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2069_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2070_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2071_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2073_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2075_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2076_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_2057_ = lean_ctor_get(v_a_2055_, 0);
v_snd_2058_ = lean_ctor_get(v_a_2055_, 1);
v_isSharedCheck_2076_ = (!lean_is_exclusive(v_a_2055_)) as u8;
if v_isSharedCheck_2076_ == 0 {
v___x_2060_ = v_a_2055_;
v_isShared_2061_ = v_isSharedCheck_2076_;
state = 1; continue;
} else {
lean_inc(v_snd_2058_);
lean_inc(v_fst_2057_);
lean_dec(v_a_2055_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2076_;
state = 1; continue;
}
}
1 => {
v___x_2062_ = lean_unsigned_to_nat(100);
v___x_2063_ = lean_nat_dec_lt(v_snd_2058_, v___x_2062_);
if v___x_2063_ == 0 {
let mut v___x_2065_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_2061_ == 0 {
v___x_2065_ = v___x_2060_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2067_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_fst_2057_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_snd_2058_);
v___x_2065_ = v_reuseFailAlloc_2067_;
state = 2; continue;
}
} else {
let mut v___x_2068_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2069_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2070_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2071_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2073_: *mut lean_object = core::ptr::null_mut(); 
v___x_2068_ = lean_box(0);
lean_inc(v_snd_2058_);
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0___redArg(v_fst_2057_, v_snd_2058_, v___x_2068_);
v___x_2070_ = lean_unsigned_to_nat(1);
v___x_2071_ = lean_nat_add(v_snd_2058_, v___x_2070_);
lean_dec(v_snd_2058_);
if v_isShared_2061_ == 0 {
lean_ctor_set(v___x_2060_, 1, v___x_2071_);
lean_ctor_set(v___x_2060_, 0, v___x_2069_);
v___x_2073_ = v___x_2060_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_2075_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2075_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00createTest_spec__1___redArg___boxed(mut v_a_2077_: *mut lean_object, mut v___y_2078_: *mut lean_object) -> *mut lean_object{
let mut v_res_2079_: *mut lean_object = core::ptr::null_mut(); 
v_res_2079_ = l___private_Init_While_0__whileM_erased___at___00createTest_spec__1___redArg(v_a_2077_);
return v_res_2079_;
}
#[no_mangle] pub unsafe extern "C" fn l_createTest() -> *mut lean_object{
let mut v___x_2081_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2082_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2083_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2084_: *mut lean_object = core::ptr::null_mut(); let mut v_set_2085_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2086_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2087_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2088_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2090_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2091_: u8 = 0; let mut v_fst_2092_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2094_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2095_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2096_: u8 = 0; let mut v_a_2097_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2099_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2100_: u8 = 0; let mut v___x_2102_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2103_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2104_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_2081_ = lean_unsigned_to_nat(0);
v___x_2082_ = lean_unsigned_to_nat(256);
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_mk_array(v___x_2082_, v___x_2083_);
v_set_2085_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_set_2085_, 0, v___x_2081_);
lean_ctor_set(v_set_2085_, 1, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2086_, 0, v_set_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2081_);
v___x_2087_ = l___private_Init_While_0__whileM_erased___at___00createTest_spec__1___redArg(v___x_2086_);
if lean_obj_tag(v___x_2087_) == 0 {
let mut v_a_2088_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2090_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2091_: u8 = 0; let mut v_isSharedCheck_2096_: u8 = 0; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2096_ = (!lean_is_exclusive(v___x_2087_)) as u8;
if v_isSharedCheck_2096_ == 0 {
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2096_;
state = 1; continue;
} else {
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2096_;
state = 1; continue;
}
} else {
let mut v_a_2097_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2099_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2100_: u8 = 0; let mut v_isSharedCheck_2104_: u8 = 0; 
v_a_2097_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2104_ = (!lean_is_exclusive(v___x_2087_)) as u8;
if v_isSharedCheck_2104_ == 0 {
v___x_2099_ = v___x_2087_;
v_isShared_2100_ = v_isSharedCheck_2104_;
state = 3; continue;
} else {
lean_inc(v_a_2097_);
lean_dec(v___x_2087_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
state = 3; continue;
}
}
}
1 => {
v_fst_2092_ = lean_ctor_get(v_a_2088_, 0);
lean_inc(v_fst_2092_);
lean_dec(v_a_2088_);
if v_isShared_2091_ == 0 {
lean_ctor_set(v___x_2090_, 0, v_fst_2092_);
v___x_2094_ = v___x_2090_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2095_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_fst_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
state = 2; continue;
}
}
3 => {
if v_isShared_2100_ == 0 {
v___x_2102_ = v___x_2099_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_2103_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_createTest___boxed(mut v_a_2105_: *mut lean_object) -> *mut lean_object{
let mut v_res_2106_: *mut lean_object = core::ptr::null_mut(); 
v_res_2106_ = l_createTest();
return v_res_2106_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0(mut v_00_u03b2_2107_: *mut lean_object, mut v_m_2108_: *mut lean_object, mut v_a_2109_: *mut lean_object, mut v_b_2110_: *mut lean_object) -> *mut lean_object{
let mut v___x_2111_: *mut lean_object = core::ptr::null_mut(); 
v___x_2111_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0___redArg(v_m_2108_, v_a_2109_, v_b_2110_);
return v___x_2111_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00createTest_spec__1(mut v_inst_2112_: *mut lean_object, mut v_a_2113_: *mut lean_object) -> *mut lean_object{
let mut v___x_2115_: *mut lean_object = core::ptr::null_mut(); 
v___x_2115_ = l___private_Init_While_0__whileM_erased___at___00createTest_spec__1___redArg(v_a_2113_);
return v___x_2115_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00createTest_spec__1___boxed(mut v_inst_2116_: *mut lean_object, mut v_a_2117_: *mut lean_object, mut v___y_2118_: *mut lean_object) -> *mut lean_object{
let mut v_res_2119_: *mut lean_object = core::ptr::null_mut(); 
v_res_2119_ = l___private_Init_While_0__whileM_erased___at___00createTest_spec__1(v_inst_2116_, v_a_2117_);
return v_res_2119_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__0(mut v_00_u03b2_2120_: *mut lean_object, mut v_a_2121_: *mut lean_object, mut v_x_2122_: *mut lean_object) -> u8{
let mut v___x_2123_: u8 = 0; 
v___x_2123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__0___redArg(v_a_2121_, v_x_2122_);
return v___x_2123_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__0___boxed(mut v_00_u03b2_2124_: *mut lean_object, mut v_a_2125_: *mut lean_object, mut v_x_2126_: *mut lean_object) -> *mut lean_object{
let mut v_res_2127_: u8 = 0; let mut v_r_2128_: *mut lean_object = core::ptr::null_mut(); 
v_res_2127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__0(v_00_u03b2_2124_, v_a_2125_, v_x_2126_);
lean_dec(v_x_2126_);
lean_dec(v_a_2125_);
v_r_2128_ = lean_box((v_res_2127_) as usize);
return v_r_2128_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1(mut v_00_u03b2_2129_: *mut lean_object, mut v_data_2130_: *mut lean_object) -> *mut lean_object{
let mut v___x_2131_: *mut lean_object = core::ptr::null_mut(); 
v___x_2131_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1___redArg(v_data_2130_);
return v___x_2131_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1_spec__2(mut v_00_u03b2_2132_: *mut lean_object, mut v_i_2133_: *mut lean_object, mut v_source_2134_: *mut lean_object, mut v_target_2135_: *mut lean_object) -> *mut lean_object{
let mut v___x_2136_: *mut lean_object = core::ptr::null_mut(); 
v___x_2136_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1_spec__2___redArg(v_i_2133_, v_source_2134_, v_target_2135_);
return v___x_2136_;
}
#[no_mangle] pub unsafe extern "C" fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1_spec__2_spec__4(mut v_00_u03b2_2137_: *mut lean_object, mut v_x_2138_: *mut lean_object, mut v_x_2139_: *mut lean_object) -> *mut lean_object{
let mut v___x_2140_: *mut lean_object = core::ptr::null_mut(); 
v___x_2140_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2138_, v_x_2139_);
return v___x_2140_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_all___at___00test_spec__0(mut v_out_2141_: *mut lean_object, mut v_x_2142_: *mut lean_object) -> u8{
let mut v___x_2143_: u8 = 0; let mut v_head_2144_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2148_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_2142_) == 0 {
let mut v___x_2143_: u8 = 0; 
v___x_2143_ = 1;
return v___x_2143_;
} else {
let mut v_head_2144_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2148_: u8 = 0; 
v_head_2144_ = lean_ctor_get(v_x_2142_, 0);
v_tail_2145_ = lean_ctor_get(v_x_2142_, 1);
v___x_2146_ = lean_nat_mod(v_out_2141_, v_head_2144_);
v___x_2147_ = lean_unsigned_to_nat(0);
v___x_2148_ = lean_nat_dec_eq(v___x_2146_, v___x_2147_);
lean_dec(v___x_2146_);
if v___x_2148_ == 0 {
return v___x_2148_;
} else {
v_x_2142_ = v_tail_2145_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_all___at___00test_spec__0___boxed(mut v_out_2150_: *mut lean_object, mut v_x_2151_: *mut lean_object) -> *mut lean_object{
let mut v_res_2152_: u8 = 0; let mut v_r_2153_: *mut lean_object = core::ptr::null_mut(); 
v_res_2152_ = l_List_all___at___00test_spec__0(v_out_2150_, v_x_2151_);
lean_dec(v_x_2151_);
lean_dec(v_out_2150_);
v_r_2153_ = lean_box((v_res_2152_) as usize);
return v_r_2153_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00test_spec__1___redArg(mut v_a_2154_: *mut lean_object, mut v_b_2155_: u8) -> u8{
let mut v_it_u2082_2156_: *mut lean_object = core::ptr::null_mut(); let mut v_it_u2081_2157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2159_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2160_: u8 = 0; let mut v_array_2161_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_2162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2164_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2165_: u8 = 0; let mut v___x_2166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2167_: u8 = 0; let mut v___x_2168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2172_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2175_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2177_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2178_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2179_: u8 = 0; let mut v_isSharedCheck_2180_: u8 = 0; let mut v_unused_2181_: *mut lean_object = core::ptr::null_mut(); let mut v_val_2182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2184_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2185_: u8 = 0; let mut v_it_u2081_2186_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2188_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2189_: u8 = 0; let mut v___x_2190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2192_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2194_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2195_: u8 = 0; let mut v_unused_2196_: *mut lean_object = core::ptr::null_mut(); let mut v_it_u2081_2197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2199_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2200_: u8 = 0; let mut v_key_2201_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2203_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2206_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2209_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2210_: u8 = 0; let mut v___x_2212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2214_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2216_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2217_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2218_: u8 = 0; let mut v_unused_2219_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2220_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_it_u2082_2156_ = lean_ctor_get(v_a_2154_, 1);
lean_inc(v_it_u2082_2156_);
if lean_obj_tag(v_it_u2082_2156_) == 0 {
let mut v_it_u2081_2157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2159_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2160_: u8 = 0; let mut v_isSharedCheck_2180_: u8 = 0; 
v_it_u2081_2157_ = lean_ctor_get(v_a_2154_, 0);
v_isSharedCheck_2180_ = (!lean_is_exclusive(v_a_2154_)) as u8;
if v_isSharedCheck_2180_ == 0 {
let mut v_unused_2181_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2181_ = lean_ctor_get(v_a_2154_, 1);
lean_dec(v_unused_2181_);
v___x_2159_ = v_a_2154_;
v_isShared_2160_ = v_isSharedCheck_2180_;
state = 1; continue;
} else {
lean_inc(v_it_u2081_2157_);
lean_dec(v_a_2154_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2180_;
state = 1; continue;
}
} else {
let mut v_val_2182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2184_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2185_: u8 = 0; let mut v_isSharedCheck_2220_: u8 = 0; 
v_val_2182_ = lean_ctor_get(v_it_u2082_2156_, 0);
v_isSharedCheck_2220_ = (!lean_is_exclusive(v_it_u2082_2156_)) as u8;
if v_isSharedCheck_2220_ == 0 {
v___x_2184_ = v_it_u2082_2156_;
v_isShared_2185_ = v_isSharedCheck_2220_;
state = 5; continue;
} else {
lean_inc(v_val_2182_);
lean_dec(v_it_u2082_2156_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2220_;
state = 5; continue;
}
}
}
1 => {
v_array_2161_ = lean_ctor_get(v_it_u2081_2157_, 0);
v_pos_2162_ = lean_ctor_get(v_it_u2081_2157_, 1);
v_isSharedCheck_2179_ = (!lean_is_exclusive(v_it_u2081_2157_)) as u8;
if v_isSharedCheck_2179_ == 0 {
v___x_2164_ = v_it_u2081_2157_;
v_isShared_2165_ = v_isSharedCheck_2179_;
state = 2; continue;
} else {
lean_inc(v_pos_2162_);
lean_inc(v_array_2161_);
lean_dec(v_it_u2081_2157_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2179_;
state = 2; continue;
}
}
5 => {
if lean_obj_tag(v_val_2182_) == 0 {
let mut v_it_u2081_2186_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2188_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2189_: u8 = 0; let mut v_isSharedCheck_2195_: u8 = 0; 
lean_del_object(v___x_2184_);
v_it_u2081_2186_ = lean_ctor_get(v_a_2154_, 0);
v_isSharedCheck_2195_ = (!lean_is_exclusive(v_a_2154_)) as u8;
if v_isSharedCheck_2195_ == 0 {
let mut v_unused_2196_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2196_ = lean_ctor_get(v_a_2154_, 1);
lean_dec(v_unused_2196_);
v___x_2188_ = v_a_2154_;
v_isShared_2189_ = v_isSharedCheck_2195_;
state = 6; continue;
} else {
lean_inc(v_it_u2081_2186_);
lean_dec(v_a_2154_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2195_;
state = 6; continue;
}
} else {
let mut v_it_u2081_2197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2199_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2200_: u8 = 0; let mut v_isSharedCheck_2218_: u8 = 0; 
v_it_u2081_2197_ = lean_ctor_get(v_a_2154_, 0);
v_isSharedCheck_2218_ = (!lean_is_exclusive(v_a_2154_)) as u8;
if v_isSharedCheck_2218_ == 0 {
let mut v_unused_2219_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2219_ = lean_ctor_get(v_a_2154_, 1);
lean_dec(v_unused_2219_);
v___x_2199_ = v_a_2154_;
v_isShared_2200_ = v_isSharedCheck_2218_;
state = 8; continue;
} else {
lean_inc(v_it_u2081_2197_);
lean_dec(v_a_2154_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2218_;
state = 8; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00test_spec__1___redArg___boxed(mut v_a_2221_: *mut lean_object, mut v_b_2222_: *mut lean_object) -> *mut lean_object{
let mut v_b_boxed_2223_: u8 = 0; let mut v_res_2224_: u8 = 0; let mut v_r_2225_: *mut lean_object = core::ptr::null_mut(); 
v_b_boxed_2223_ = (lean_unbox(v_b_2222_) as u8);
v_res_2224_ = l_WellFounded_opaqueFix_u2083___at___00test_spec__1___redArg(v_a_2221_, v_b_boxed_2223_);
v_r_2225_ = lean_box((v_res_2224_) as usize);
return v_r_2225_;
}
#[no_mangle] pub unsafe extern "C" fn l_test() -> *mut lean_object{
let mut v___x_2227_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2230_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2231_: u8 = 0; let mut v___x_2233_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2235_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2236_: *mut lean_object = core::ptr::null_mut(); let mut v___y_2238_: u8 = 0; let mut v___x_2239_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2241_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_2242_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2244_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2245_: u8 = 0; let mut v___x_2246_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2248_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2249_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2250_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2251_: u8 = 0; let mut v___x_2252_: u8 = 0; let mut v_reuseFailAlloc_2253_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2254_: u8 = 0; let mut v_unused_2255_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2256_: u8 = 0; let mut v_a_2257_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2259_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2260_: u8 = 0; let mut v___x_2262_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2263_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2264_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_2227_ = l_createTest();
if lean_obj_tag(v___x_2227_) == 0 {
let mut v_a_2228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2230_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2231_: u8 = 0; let mut v_isSharedCheck_2256_: u8 = 0; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2256_ = (!lean_is_exclusive(v___x_2227_)) as u8;
if v_isSharedCheck_2256_ == 0 {
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2256_;
state = 1; continue;
} else {
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2256_;
state = 1; continue;
}
} else {
let mut v_a_2257_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2259_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2260_: u8 = 0; let mut v_isSharedCheck_2264_: u8 = 0; 
v_a_2257_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2264_ = (!lean_is_exclusive(v___x_2227_)) as u8;
if v_isSharedCheck_2264_ == 0 {
v___x_2259_ = v___x_2227_;
v_isShared_2260_ = v_isSharedCheck_2264_;
state = 7; continue;
} else {
lean_inc(v_a_2257_);
lean_dec(v___x_2227_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
state = 7; continue;
}
}
}
1 => {
v_buckets_2242_ = lean_ctor_get(v_a_2228_, 1);
v_isSharedCheck_2254_ = (!lean_is_exclusive(v_a_2228_)) as u8;
if v_isSharedCheck_2254_ == 0 {
let mut v_unused_2255_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2255_ = lean_ctor_get(v_a_2228_, 0);
lean_dec(v_unused_2255_);
v___x_2244_ = v_a_2228_;
v_isShared_2245_ = v_isSharedCheck_2254_;
state = 5; continue;
} else {
lean_inc(v_buckets_2242_);
lean_dec(v_a_2228_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2254_;
state = 5; continue;
}
}
7 => {
if v_isShared_2260_ == 0 {
v___x_2262_ = v___x_2259_;
state = 8; continue;
} else {
let mut v_reuseFailAlloc_2263_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
state = 8; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_test___boxed(mut v_a_2265_: *mut lean_object) -> *mut lean_object{
let mut v_res_2266_: *mut lean_object = core::ptr::null_mut(); 
v_res_2266_ = l_test();
return v_res_2266_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00test_spec__1(mut v_inst_2267_: *mut lean_object, mut v_R_2268_: *mut lean_object, mut v_a_2269_: *mut lean_object, mut v_b_2270_: u8, mut v_c_2271_: *mut lean_object) -> u8{
let mut v___x_2272_: u8 = 0; 
v___x_2272_ = l_WellFounded_opaqueFix_u2083___at___00test_spec__1___redArg(v_a_2269_, v_b_2270_);
return v___x_2272_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00test_spec__1___boxed(mut v_inst_2273_: *mut lean_object, mut v_R_2274_: *mut lean_object, mut v_a_2275_: *mut lean_object, mut v_b_2276_: *mut lean_object, mut v_c_2277_: *mut lean_object) -> *mut lean_object{
let mut v_b_boxed_2278_: u8 = 0; let mut v_res_2279_: u8 = 0; let mut v_r_2280_: *mut lean_object = core::ptr::null_mut(); 
v_b_boxed_2278_ = (lean_unbox(v_b_2276_) as u8);
v_res_2279_ = l_WellFounded_opaqueFix_u2083___at___00test_spec__1(v_inst_2273_, v_R_2274_, v_a_2275_, v_b_boxed_2278_, v_c_2277_);
v_r_2280_ = lean_box((v_res_2279_) as usize);
return v_r_2280_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__1___redArg(mut v_a_2281_: *mut lean_object) -> *mut lean_object{
let mut v___x_2283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2285_: u8 = 0; let mut v___x_2286_: *mut lean_object = core::ptr::null_mut(); let mut v_i_2287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2288_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_2283_ = l_testPrimes;
v___x_2284_ = l_List_lengthTR___redArg(v___x_2283_);
v___x_2285_ = lean_nat_dec_lt(v_a_2281_, v___x_2284_);
lean_dec(v___x_2284_);
if v___x_2285_ == 0 {
let mut v___x_2286_: *mut lean_object = core::ptr::null_mut(); 
v___x_2286_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_2286_, 0, v_a_2281_);
return v___x_2286_;
} else {
let mut v_i_2287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2288_: *mut lean_object = core::ptr::null_mut(); 
v_i_2287_ = lean_unsigned_to_nat(1);
v___x_2288_ = lean_nat_add(v_a_2281_, v_i_2287_);
lean_dec(v_a_2281_);
v_a_2281_ = v___x_2288_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__1___redArg___boxed(mut v_a_2290_: *mut lean_object, mut v___y_2291_: *mut lean_object) -> *mut lean_object{
let mut v_res_2292_: *mut lean_object = core::ptr::null_mut(); 
v_res_2292_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__1___redArg(v_a_2290_);
return v_res_2292_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchNativeAny___lam__0(mut v___x_2293_: *mut lean_object) -> *mut lean_object{
let mut v___x_2295_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2297_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2298_: u8 = 0; let mut v___x_2299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2301_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2302_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2303_: u8 = 0; let mut v_unused_2304_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2307_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2308_: u8 = 0; let mut v___x_2310_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2311_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2312_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_2295_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__1___redArg(v___x_2293_);
if lean_obj_tag(v___x_2295_) == 0 {
let mut v___x_2297_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2298_: u8 = 0; let mut v_isSharedCheck_2303_: u8 = 0; 
v_isSharedCheck_2303_ = (!lean_is_exclusive(v___x_2295_)) as u8;
if v_isSharedCheck_2303_ == 0 {
let mut v_unused_2304_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2304_ = lean_ctor_get(v___x_2295_, 0);
lean_dec(v_unused_2304_);
v___x_2297_ = v___x_2295_;
v_isShared_2298_ = v_isSharedCheck_2303_;
state = 1; continue;
} else {
lean_dec(v___x_2295_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2303_;
state = 1; continue;
}
} else {
let mut v_a_2305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2307_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2308_: u8 = 0; let mut v_isSharedCheck_2312_: u8 = 0; 
v_a_2305_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2312_ = (!lean_is_exclusive(v___x_2295_)) as u8;
if v_isSharedCheck_2312_ == 0 {
v___x_2307_ = v___x_2295_;
v_isShared_2308_ = v_isSharedCheck_2312_;
state = 3; continue;
} else {
lean_inc(v_a_2305_);
lean_dec(v___x_2295_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
state = 3; continue;
}
}
}
1 => {
v___x_2299_ = lean_box(0);
if v_isShared_2298_ == 0 {
lean_ctor_set(v___x_2297_, 0, v___x_2299_);
v___x_2301_ = v___x_2297_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2302_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
state = 2; continue;
}
}
3 => {
if v_isShared_2308_ == 0 {
v___x_2310_ = v___x_2307_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_2311_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchNativeAny___lam__0___boxed(mut v___x_2313_: *mut lean_object, mut v___y_2314_: *mut lean_object) -> *mut lean_object{
let mut v_res_2315_: *mut lean_object = core::ptr::null_mut(); 
v_res_2315_ = l_benchNativeAny___lam__0(v___x_2313_);
return v_res_2315_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0___redArg(mut v_size_2316_: *mut lean_object, mut v_a_2317_: *mut lean_object) -> *mut lean_object{
let mut v_fst_2319_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_2320_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2322_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2323_: u8 = 0; let mut v___x_2324_: u8 = 0; let mut v___x_2326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2327_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2328_: *mut lean_object = core::ptr::null_mut(); let mut v_i_2329_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2334_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2336_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2337_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_2319_ = lean_ctor_get(v_a_2317_, 0);
v_snd_2320_ = lean_ctor_get(v_a_2317_, 1);
v_isSharedCheck_2337_ = (!lean_is_exclusive(v_a_2317_)) as u8;
if v_isSharedCheck_2337_ == 0 {
v___x_2322_ = v_a_2317_;
v_isShared_2323_ = v_isSharedCheck_2337_;
state = 1; continue;
} else {
lean_inc(v_snd_2320_);
lean_inc(v_fst_2319_);
lean_dec(v_a_2317_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2337_;
state = 1; continue;
}
}
1 => {
v___x_2324_ = lean_nat_dec_lt(v_snd_2320_, v_size_2316_);
if v___x_2324_ == 0 {
let mut v___x_2326_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_2323_ == 0 {
v___x_2326_ = v___x_2322_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2328_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_fst_2319_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_snd_2320_);
v___x_2326_ = v_reuseFailAlloc_2328_;
state = 2; continue;
}
} else {
let mut v_i_2329_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2334_: *mut lean_object = core::ptr::null_mut(); 
v_i_2329_ = lean_unsigned_to_nat(1);
v___x_2330_ = lean_box(0);
lean_inc(v_snd_2320_);
v___x_2331_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00createTest_spec__0___redArg(v_fst_2319_, v_snd_2320_, v___x_2330_);
v___x_2332_ = lean_nat_add(v_snd_2320_, v_i_2329_);
lean_dec(v_snd_2320_);
if v_isShared_2323_ == 0 {
lean_ctor_set(v___x_2322_, 1, v___x_2332_);
lean_ctor_set(v___x_2322_, 0, v___x_2331_);
v___x_2334_ = v___x_2322_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_2336_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2336_;
state = 3; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0___redArg___boxed(mut v_size_2338_: *mut lean_object, mut v_a_2339_: *mut lean_object, mut v___y_2340_: *mut lean_object) -> *mut lean_object{
let mut v_res_2341_: *mut lean_object = core::ptr::null_mut(); 
v_res_2341_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0___redArg(v_size_2338_, v_a_2339_);
lean_dec(v_size_2338_);
return v_res_2341_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchNativeAny(mut v_size_2342_: *mut lean_object) -> *mut lean_object{
let mut v___x_2344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2345_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2348_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2349_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2351_: *mut lean_object = core::ptr::null_mut(); let mut v_set_2352_: *mut lean_object = core::ptr::null_mut(); let mut v_i_2353_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2354_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2355_: *mut lean_object = core::ptr::null_mut(); let mut v___f_2356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2357_: *mut lean_object = core::ptr::null_mut(); let mut v_checks_2358_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2359_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2362_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2363_: u8 = 0; let mut v___x_2365_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2366_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2367_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_2344_ = lean_unsigned_to_nat(0);
v___x_2345_ = lean_unsigned_to_nat(4);
v___x_2346_ = lean_nat_mul(v_size_2342_, v___x_2345_);
v___x_2347_ = lean_unsigned_to_nat(3);
v___x_2348_ = lean_nat_div(v___x_2346_, v___x_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = l_Nat_nextPowerOfTwo(v___x_2348_);
lean_dec(v___x_2348_);
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_mk_array(v___x_2349_, v___x_2350_);
v_set_2352_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_set_2352_, 0, v___x_2344_);
lean_ctor_set(v_set_2352_, 1, v___x_2351_);
v_i_2353_ = lean_unsigned_to_nat(1);
v___x_2354_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2354_, 0, v_set_2352_);
lean_ctor_set(v___x_2354_, 1, v_i_2353_);
v___x_2355_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0___redArg(v_size_2342_, v___x_2354_);
if lean_obj_tag(v___x_2355_) == 0 {
let mut v___f_2356_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2357_: *mut lean_object = core::ptr::null_mut(); let mut v_checks_2358_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2359_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_2355_, 1);
v___f_2356_ = lean_alloc_closure(l_benchNativeAny___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_2356_, 0, v___x_2344_);
v___x_2357_ = lean_unsigned_to_nat(100);
v_checks_2358_ = lean_nat_mul(v_size_2342_, v___x_2357_);
v___x_2359_ = l_timeNanos(v_checks_2358_, v___f_2356_);
return v___x_2359_;
} else {
let mut v_a_2360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2362_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2363_: u8 = 0; let mut v_isSharedCheck_2367_: u8 = 0; 
v_a_2360_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2367_ = (!lean_is_exclusive(v___x_2355_)) as u8;
if v_isSharedCheck_2367_ == 0 {
v___x_2362_ = v___x_2355_;
v_isShared_2363_ = v_isSharedCheck_2367_;
state = 1; continue;
} else {
lean_inc(v_a_2360_);
lean_dec(v___x_2355_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
state = 1; continue;
}
}
}
1 => {
if v_isShared_2363_ == 0 {
v___x_2365_ = v___x_2362_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2366_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchNativeAny___boxed(mut v_size_2368_: *mut lean_object, mut v_a_2369_: *mut lean_object) -> *mut lean_object{
let mut v_res_2370_: *mut lean_object = core::ptr::null_mut(); 
v_res_2370_ = l_benchNativeAny(v_size_2368_);
lean_dec(v_size_2368_);
return v_res_2370_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0(mut v_size_2371_: *mut lean_object, mut v_inst_2372_: *mut lean_object, mut v_a_2373_: *mut lean_object) -> *mut lean_object{
let mut v___x_2375_: *mut lean_object = core::ptr::null_mut(); 
v___x_2375_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0___redArg(v_size_2371_, v_a_2373_);
return v___x_2375_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0___boxed(mut v_size_2376_: *mut lean_object, mut v_inst_2377_: *mut lean_object, mut v_a_2378_: *mut lean_object, mut v___y_2379_: *mut lean_object) -> *mut lean_object{
let mut v_res_2380_: *mut lean_object = core::ptr::null_mut(); 
v_res_2380_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0(v_size_2376_, v_inst_2377_, v_a_2378_);
lean_dec(v_size_2376_);
return v_res_2380_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__1(mut v_inst_2381_: *mut lean_object, mut v_a_2382_: *mut lean_object) -> *mut lean_object{
let mut v___x_2384_: *mut lean_object = core::ptr::null_mut(); 
v___x_2384_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__1___redArg(v_a_2382_);
return v___x_2384_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__1___boxed(mut v_inst_2385_: *mut lean_object, mut v_a_2386_: *mut lean_object, mut v___y_2387_: *mut lean_object) -> *mut lean_object{
let mut v_res_2388_: *mut lean_object = core::ptr::null_mut(); 
v_res_2388_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__1(v_inst_2385_, v_a_2386_);
return v_res_2388_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_all___at___00benchIterAny_spec__0(mut v_out_2389_: *mut lean_object, mut v_x_2390_: *mut lean_object) -> u8{
let mut v___x_2391_: u8 = 0; let mut v_head_2392_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2396_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_2390_) == 0 {
let mut v___x_2391_: u8 = 0; 
v___x_2391_ = 1;
return v___x_2391_;
} else {
let mut v_head_2392_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2396_: u8 = 0; 
v_head_2392_ = lean_ctor_get(v_x_2390_, 0);
v_tail_2393_ = lean_ctor_get(v_x_2390_, 1);
v___x_2394_ = lean_unsigned_to_nat(0);
v___x_2395_ = lean_nat_mod(v_out_2389_, v_head_2392_);
v___x_2396_ = lean_nat_dec_eq(v___x_2395_, v___x_2394_);
lean_dec(v___x_2395_);
if v___x_2396_ == 0 {
return v___x_2396_;
} else {
v_x_2390_ = v_tail_2393_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_all___at___00benchIterAny_spec__0___boxed(mut v_out_2398_: *mut lean_object, mut v_x_2399_: *mut lean_object) -> *mut lean_object{
let mut v_res_2400_: u8 = 0; let mut v_r_2401_: *mut lean_object = core::ptr::null_mut(); 
v_res_2400_ = l_List_all___at___00benchIterAny_spec__0(v_out_2398_, v_x_2399_);
lean_dec(v_x_2399_);
lean_dec(v_out_2398_);
v_r_2401_ = lean_box((v_res_2400_) as usize);
return v_r_2401_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchIterAny_spec__1___redArg(mut v_b_2402_: *mut lean_object, mut v_a_2403_: *mut lean_object, mut v_b_2404_: u8) -> u8{
let mut v_it_u2082_2405_: *mut lean_object = core::ptr::null_mut(); let mut v_it_u2081_2406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2408_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2409_: u8 = 0; let mut v_array_2410_: *mut lean_object = core::ptr::null_mut(); let mut v_pos_2411_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2413_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2414_: u8 = 0; let mut v___x_2415_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2416_: u8 = 0; let mut v___x_2417_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2418_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2420_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2421_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2422_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2424_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2426_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2427_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2428_: u8 = 0; let mut v_isSharedCheck_2429_: u8 = 0; let mut v_unused_2430_: *mut lean_object = core::ptr::null_mut(); let mut v_val_2431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2433_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2434_: u8 = 0; let mut v_it_u2081_2435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2437_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2438_: u8 = 0; let mut v___x_2439_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2441_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2443_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2444_: u8 = 0; let mut v_unused_2445_: *mut lean_object = core::ptr::null_mut(); let mut v_it_u2081_2446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2448_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2449_: u8 = 0; let mut v_key_2450_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2453_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2454_: u8 = 0; let mut v___x_2456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2458_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2460_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2461_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2462_: u8 = 0; let mut v_unused_2463_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2464_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_it_u2082_2405_ = lean_ctor_get(v_a_2403_, 1);
lean_inc(v_it_u2082_2405_);
if lean_obj_tag(v_it_u2082_2405_) == 0 {
let mut v_it_u2081_2406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2408_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2409_: u8 = 0; let mut v_isSharedCheck_2429_: u8 = 0; 
v_it_u2081_2406_ = lean_ctor_get(v_a_2403_, 0);
v_isSharedCheck_2429_ = (!lean_is_exclusive(v_a_2403_)) as u8;
if v_isSharedCheck_2429_ == 0 {
let mut v_unused_2430_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2430_ = lean_ctor_get(v_a_2403_, 1);
lean_dec(v_unused_2430_);
v___x_2408_ = v_a_2403_;
v_isShared_2409_ = v_isSharedCheck_2429_;
state = 1; continue;
} else {
lean_inc(v_it_u2081_2406_);
lean_dec(v_a_2403_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2429_;
state = 1; continue;
}
} else {
let mut v_val_2431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2433_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2434_: u8 = 0; let mut v_isSharedCheck_2464_: u8 = 0; 
v_val_2431_ = lean_ctor_get(v_it_u2082_2405_, 0);
v_isSharedCheck_2464_ = (!lean_is_exclusive(v_it_u2082_2405_)) as u8;
if v_isSharedCheck_2464_ == 0 {
v___x_2433_ = v_it_u2082_2405_;
v_isShared_2434_ = v_isSharedCheck_2464_;
state = 5; continue;
} else {
lean_inc(v_val_2431_);
lean_dec(v_it_u2082_2405_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2464_;
state = 5; continue;
}
}
}
1 => {
v_array_2410_ = lean_ctor_get(v_it_u2081_2406_, 0);
v_pos_2411_ = lean_ctor_get(v_it_u2081_2406_, 1);
v_isSharedCheck_2428_ = (!lean_is_exclusive(v_it_u2081_2406_)) as u8;
if v_isSharedCheck_2428_ == 0 {
v___x_2413_ = v_it_u2081_2406_;
v_isShared_2414_ = v_isSharedCheck_2428_;
state = 2; continue;
} else {
lean_inc(v_pos_2411_);
lean_inc(v_array_2410_);
lean_dec(v_it_u2081_2406_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2428_;
state = 2; continue;
}
}
5 => {
if lean_obj_tag(v_val_2431_) == 0 {
let mut v_it_u2081_2435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2437_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2438_: u8 = 0; let mut v_isSharedCheck_2444_: u8 = 0; 
lean_del_object(v___x_2433_);
v_it_u2081_2435_ = lean_ctor_get(v_a_2403_, 0);
v_isSharedCheck_2444_ = (!lean_is_exclusive(v_a_2403_)) as u8;
if v_isSharedCheck_2444_ == 0 {
let mut v_unused_2445_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2445_ = lean_ctor_get(v_a_2403_, 1);
lean_dec(v_unused_2445_);
v___x_2437_ = v_a_2403_;
v_isShared_2438_ = v_isSharedCheck_2444_;
state = 6; continue;
} else {
lean_inc(v_it_u2081_2435_);
lean_dec(v_a_2403_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2444_;
state = 6; continue;
}
} else {
let mut v_it_u2081_2446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2448_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2449_: u8 = 0; let mut v_isSharedCheck_2462_: u8 = 0; 
v_it_u2081_2446_ = lean_ctor_get(v_a_2403_, 0);
v_isSharedCheck_2462_ = (!lean_is_exclusive(v_a_2403_)) as u8;
if v_isSharedCheck_2462_ == 0 {
let mut v_unused_2463_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2463_ = lean_ctor_get(v_a_2403_, 1);
lean_dec(v_unused_2463_);
v___x_2448_ = v_a_2403_;
v_isShared_2449_ = v_isSharedCheck_2462_;
state = 8; continue;
} else {
lean_inc(v_it_u2081_2446_);
lean_dec(v_a_2403_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2462_;
state = 8; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchIterAny_spec__1___redArg___boxed(mut v_b_2465_: *mut lean_object, mut v_a_2466_: *mut lean_object, mut v_b_2467_: *mut lean_object) -> *mut lean_object{
let mut v_b_boxed_2468_: u8 = 0; let mut v_res_2469_: u8 = 0; let mut v_r_2470_: *mut lean_object = core::ptr::null_mut(); 
v_b_boxed_2468_ = (lean_unbox(v_b_2467_) as u8);
v_res_2469_ = l_WellFounded_opaqueFix_u2083___at___00benchIterAny_spec__1___redArg(v_b_2465_, v_a_2466_, v_b_boxed_2468_);
lean_dec(v_b_2465_);
v_r_2470_ = lean_box((v_res_2469_) as usize);
return v_r_2470_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterAny_spec__2___redArg(mut v___x_2471_: *mut lean_object, mut v_a_2472_: *mut lean_object) -> *mut lean_object{
let mut v___x_2474_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2475_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2476_: u8 = 0; let mut v___x_2477_: *mut lean_object = core::ptr::null_mut(); let mut v_buckets_2478_: *mut lean_object = core::ptr::null_mut(); let mut v_i_2479_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2481_: *mut lean_object = core::ptr::null_mut(); let mut v___y_2484_: u8 = 0; let mut v___x_2485_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2488_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2490_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2491_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2492_: u8 = 0; let mut v___x_2493_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_2474_ = l_testPrimes;
v___x_2475_ = l_List_lengthTR___redArg(v___x_2474_);
v___x_2476_ = lean_nat_dec_lt(v_a_2472_, v___x_2475_);
lean_dec(v___x_2475_);
if v___x_2476_ == 0 {
let mut v___x_2477_: *mut lean_object = core::ptr::null_mut(); 
v___x_2477_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_2477_, 0, v_a_2472_);
return v___x_2477_;
} else {
let mut v_buckets_2478_: *mut lean_object = core::ptr::null_mut(); let mut v_i_2479_: *mut lean_object = core::ptr::null_mut(); let mut v___y_2484_: u8 = 0; let mut v___x_2488_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2490_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2491_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2492_: u8 = 0; let mut v___x_2493_: u8 = 0; 
v_buckets_2478_ = lean_ctor_get(v___x_2471_, 1);
v_i_2479_ = lean_unsigned_to_nat(1);
v___x_2488_ = lean_unsigned_to_nat(0);
lean_inc_ref(v_buckets_2478_);
v___x_2489_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2489_, 0, v_buckets_2478_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = 0;
v___x_2493_ = l_WellFounded_opaqueFix_u2083___at___00benchIterAny_spec__1___redArg(v_a_2472_, v___x_2491_, v___x_2492_);
if v___x_2493_ == 0 {
if v___x_2493_ == 0 {
state = 1; continue;
} else {
v___y_2484_ = v___x_2493_;
state = 2; continue;
}
} else {
v___y_2484_ = v___x_2493_;
state = 2; continue;
}
}
}
1 => {
v___x_2481_ = lean_nat_add(v_a_2472_, v_i_2479_);
lean_dec(v_a_2472_);
v_a_2472_ = v___x_2481_;
state = 0; continue;
}
2 => {
if v___y_2484_ == 0 {
let mut v___x_2485_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2487_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_2472_);
v___x_2485_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_2486_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
} else {
state = 1; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterAny_spec__2___redArg___boxed(mut v___x_2494_: *mut lean_object, mut v_a_2495_: *mut lean_object, mut v___y_2496_: *mut lean_object) -> *mut lean_object{
let mut v_res_2497_: *mut lean_object = core::ptr::null_mut(); 
v_res_2497_ = l___private_Init_While_0__whileM_erased___at___00benchIterAny_spec__2___redArg(v___x_2494_, v_a_2495_);
lean_dec_ref(v___x_2494_);
return v_res_2497_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterAny___lam__0(mut v_fst_2498_: *mut lean_object, mut v___x_2499_: *mut lean_object) -> *mut lean_object{
let mut v___x_2501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2503_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2504_: u8 = 0; let mut v___x_2505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2507_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2508_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2509_: u8 = 0; let mut v_unused_2510_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2511_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2513_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2514_: u8 = 0; let mut v___x_2516_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2517_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2518_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_2501_ = l___private_Init_While_0__whileM_erased___at___00benchIterAny_spec__2___redArg(v_fst_2498_, v___x_2499_);
if lean_obj_tag(v___x_2501_) == 0 {
let mut v___x_2503_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2504_: u8 = 0; let mut v_isSharedCheck_2509_: u8 = 0; 
v_isSharedCheck_2509_ = (!lean_is_exclusive(v___x_2501_)) as u8;
if v_isSharedCheck_2509_ == 0 {
let mut v_unused_2510_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2510_ = lean_ctor_get(v___x_2501_, 0);
lean_dec(v_unused_2510_);
v___x_2503_ = v___x_2501_;
v_isShared_2504_ = v_isSharedCheck_2509_;
state = 1; continue;
} else {
lean_dec(v___x_2501_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2509_;
state = 1; continue;
}
} else {
let mut v_a_2511_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2513_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2514_: u8 = 0; let mut v_isSharedCheck_2518_: u8 = 0; 
v_a_2511_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2518_ = (!lean_is_exclusive(v___x_2501_)) as u8;
if v_isSharedCheck_2518_ == 0 {
v___x_2513_ = v___x_2501_;
v_isShared_2514_ = v_isSharedCheck_2518_;
state = 3; continue;
} else {
lean_inc(v_a_2511_);
lean_dec(v___x_2501_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
state = 3; continue;
}
}
}
1 => {
v___x_2505_ = lean_box(0);
if v_isShared_2504_ == 0 {
lean_ctor_set(v___x_2503_, 0, v___x_2505_);
v___x_2507_ = v___x_2503_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2508_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
state = 2; continue;
}
}
3 => {
if v_isShared_2514_ == 0 {
v___x_2516_ = v___x_2513_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_2517_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterAny___lam__0___boxed(mut v_fst_2519_: *mut lean_object, mut v___x_2520_: *mut lean_object, mut v___y_2521_: *mut lean_object) -> *mut lean_object{
let mut v_res_2522_: *mut lean_object = core::ptr::null_mut(); 
v_res_2522_ = l_benchIterAny___lam__0(v_fst_2519_, v___x_2520_);
lean_dec(v_fst_2519_);
return v_res_2522_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterAny(mut v_size_2523_: *mut lean_object) -> *mut lean_object{
let mut v___x_2525_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2526_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2527_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2528_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2529_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2530_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2531_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2532_: *mut lean_object = core::ptr::null_mut(); let mut v_set_2533_: *mut lean_object = core::ptr::null_mut(); let mut v_i_2534_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2535_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2536_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2537_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_2538_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2539_: *mut lean_object = core::ptr::null_mut(); let mut v_checks_2540_: *mut lean_object = core::ptr::null_mut(); let mut v___f_2541_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2542_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2543_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2545_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2546_: u8 = 0; let mut v___x_2548_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2549_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2550_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_2525_ = lean_unsigned_to_nat(0);
v___x_2526_ = lean_unsigned_to_nat(4);
v___x_2527_ = lean_nat_mul(v_size_2523_, v___x_2526_);
v___x_2528_ = lean_unsigned_to_nat(3);
v___x_2529_ = lean_nat_div(v___x_2527_, v___x_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = l_Nat_nextPowerOfTwo(v___x_2529_);
lean_dec(v___x_2529_);
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_mk_array(v___x_2530_, v___x_2531_);
v_set_2533_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_set_2533_, 0, v___x_2525_);
lean_ctor_set(v_set_2533_, 1, v___x_2532_);
v_i_2534_ = lean_unsigned_to_nat(1);
v___x_2535_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2535_, 0, v_set_2533_);
lean_ctor_set(v___x_2535_, 1, v_i_2534_);
v___x_2536_ = l___private_Init_While_0__whileM_erased___at___00benchNativeAny_spec__0___redArg(v_size_2523_, v___x_2535_);
if lean_obj_tag(v___x_2536_) == 0 {
let mut v_a_2537_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_2538_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2539_: *mut lean_object = core::ptr::null_mut(); let mut v_checks_2540_: *mut lean_object = core::ptr::null_mut(); let mut v___f_2541_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2542_: *mut lean_object = core::ptr::null_mut(); 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v_fst_2538_ = lean_ctor_get(v_a_2537_, 0);
lean_inc(v_fst_2538_);
lean_dec(v_a_2537_);
v___x_2539_ = lean_unsigned_to_nat(100);
v_checks_2540_ = lean_nat_mul(v_size_2523_, v___x_2539_);
v___f_2541_ = lean_alloc_closure(l_benchIterAny___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_2541_, 0, v_fst_2538_);
lean_closure_set(v___f_2541_, 1, v___x_2525_);
v___x_2542_ = l_timeNanos(v_checks_2540_, v___f_2541_);
return v___x_2542_;
} else {
let mut v_a_2543_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2545_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2546_: u8 = 0; let mut v_isSharedCheck_2550_: u8 = 0; 
v_a_2543_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2550_ = (!lean_is_exclusive(v___x_2536_)) as u8;
if v_isSharedCheck_2550_ == 0 {
v___x_2545_ = v___x_2536_;
v_isShared_2546_ = v_isSharedCheck_2550_;
state = 1; continue;
} else {
lean_inc(v_a_2543_);
lean_dec(v___x_2536_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
state = 1; continue;
}
}
}
1 => {
if v_isShared_2546_ == 0 {
v___x_2548_ = v___x_2545_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2549_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterAny___boxed(mut v_size_2551_: *mut lean_object, mut v_a_2552_: *mut lean_object) -> *mut lean_object{
let mut v_res_2553_: *mut lean_object = core::ptr::null_mut(); 
v_res_2553_ = l_benchIterAny(v_size_2551_);
lean_dec(v_size_2551_);
return v_res_2553_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchIterAny_spec__1(mut v_b_2554_: *mut lean_object, mut v_inst_2555_: *mut lean_object, mut v_R_2556_: *mut lean_object, mut v_a_2557_: *mut lean_object, mut v_b_2558_: u8, mut v_c_2559_: *mut lean_object) -> u8{
let mut v___x_2560_: u8 = 0; 
v___x_2560_ = l_WellFounded_opaqueFix_u2083___at___00benchIterAny_spec__1___redArg(v_b_2554_, v_a_2557_, v_b_2558_);
return v___x_2560_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchIterAny_spec__1___boxed(mut v_b_2561_: *mut lean_object, mut v_inst_2562_: *mut lean_object, mut v_R_2563_: *mut lean_object, mut v_a_2564_: *mut lean_object, mut v_b_2565_: *mut lean_object, mut v_c_2566_: *mut lean_object) -> *mut lean_object{
let mut v_b_boxed_2567_: u8 = 0; let mut v_res_2568_: u8 = 0; let mut v_r_2569_: *mut lean_object = core::ptr::null_mut(); 
v_b_boxed_2567_ = (lean_unbox(v_b_2565_) as u8);
v_res_2568_ = l_WellFounded_opaqueFix_u2083___at___00benchIterAny_spec__1(v_b_2561_, v_inst_2562_, v_R_2563_, v_a_2564_, v_b_boxed_2567_, v_c_2566_);
lean_dec(v_b_2561_);
v_r_2569_ = lean_box((v_res_2568_) as usize);
return v_r_2569_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterAny_spec__2(mut v___x_2570_: *mut lean_object, mut v_inst_2571_: *mut lean_object, mut v_a_2572_: *mut lean_object) -> *mut lean_object{
let mut v___x_2574_: *mut lean_object = core::ptr::null_mut(); 
v___x_2574_ = l___private_Init_While_0__whileM_erased___at___00benchIterAny_spec__2___redArg(v___x_2570_, v_a_2572_);
return v___x_2574_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterAny_spec__2___boxed(mut v___x_2575_: *mut lean_object, mut v_inst_2576_: *mut lean_object, mut v_a_2577_: *mut lean_object, mut v___y_2578_: *mut lean_object) -> *mut lean_object{
let mut v_res_2579_: *mut lean_object = core::ptr::null_mut(); 
v_res_2579_ = l___private_Init_While_0__whileM_erased___at___00benchIterAny_spec__2(v___x_2575_, v_inst_2576_, v_a_2577_);
lean_dec_ref(v___x_2575_);
return v_res_2579_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00compareAnyBench_spec__1_spec__1(mut v_s_2580_: *mut lean_object) -> *mut lean_object{
let mut v___x_2582_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_2583_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2584_: *mut lean_object = core::ptr::null_mut(); 
v___x_2582_ = lean_get_stdout();
v_putStr_2583_ = lean_ctor_get(v___x_2582_, 4);
lean_inc_ref(v_putStr_2583_);
lean_dec_ref(v___x_2582_);
v___x_2584_ = lean_apply_2(v_putStr_2583_, v_s_2580_, lean_box(0));
return v___x_2584_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00compareAnyBench_spec__1_spec__1___boxed(mut v_s_2585_: *mut lean_object, mut v_a_2586_: *mut lean_object) -> *mut lean_object{
let mut v_res_2587_: *mut lean_object = core::ptr::null_mut(); 
v_res_2587_ = l_IO_print___at___00IO_println___at___00compareAnyBench_spec__1_spec__1(v_s_2585_);
return v_res_2587_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00compareAnyBench_spec__1(mut v_s_2588_: *mut lean_object) -> *mut lean_object{
let mut v___x_2590_: u32 = 0; let mut v___x_2591_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2592_: *mut lean_object = core::ptr::null_mut(); 
v___x_2590_ = 10;
v___x_2591_ = lean_string_push(v_s_2588_, v___x_2590_);
v___x_2592_ = l_IO_print___at___00IO_println___at___00compareAnyBench_spec__1_spec__1(v___x_2591_);
return v___x_2592_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00compareAnyBench_spec__1___boxed(mut v_s_2593_: *mut lean_object, mut v_a_2594_: *mut lean_object) -> *mut lean_object{
let mut v_res_2595_: *mut lean_object = core::ptr::null_mut(); 
v_res_2595_ = l_IO_println___at___00compareAnyBench_spec__1(v_s_2593_);
return v_res_2595_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00compareAnyBench_spec__0___redArg(mut v_as_x27_2596_: *mut lean_object, mut v_b_2597_: *mut lean_object) -> *mut lean_object{
let mut v___x_2599_: *mut lean_object = core::ptr::null_mut(); let mut v_head_2600_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2601_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2602_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2603_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2604_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2605_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_2606_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_2607_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2609_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2610_: u8 = 0; let mut v___x_2611_: f64 = 0.0; let mut v___x_2612_: f64 = 0.0; let mut v___x_2613_: u8 = 0; let mut v___x_2614_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2615_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2617_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2619_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2620_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2623_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2625_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2626_: u8 = 0; let mut v_a_2627_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2629_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2630_: u8 = 0; let mut v___x_2632_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2633_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2634_: u8 = 0; let mut v_a_2635_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2637_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2638_: u8 = 0; let mut v___x_2640_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2641_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2642_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_as_x27_2596_) == 0 {
let mut v___x_2599_: *mut lean_object = core::ptr::null_mut(); 
v___x_2599_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_2599_, 0, v_b_2597_);
return v___x_2599_;
} else {
let mut v_head_2600_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2601_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2602_: *mut lean_object = core::ptr::null_mut(); 
v_head_2600_ = lean_ctor_get(v_as_x27_2596_, 0);
v_tail_2601_ = lean_ctor_get(v_as_x27_2596_, 1);
v___x_2602_ = l_benchNativeAny(v_head_2600_);
if lean_obj_tag(v___x_2602_) == 0 {
let mut v_a_2603_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2604_: *mut lean_object = core::ptr::null_mut(); 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v___x_2604_ = l_benchIterAny(v_head_2600_);
if lean_obj_tag(v___x_2604_) == 0 {
let mut v_a_2605_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_2606_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_2607_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2609_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2610_: u8 = 0; let mut v_isSharedCheck_2626_: u8 = 0; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v_fst_2606_ = lean_ctor_get(v_b_2597_, 0);
v_snd_2607_ = lean_ctor_get(v_b_2597_, 1);
v_isSharedCheck_2626_ = (!lean_is_exclusive(v_b_2597_)) as u8;
if v_isSharedCheck_2626_ == 0 {
v___x_2609_ = v_b_2597_;
v_isShared_2610_ = v_isSharedCheck_2626_;
state = 1; continue;
} else {
lean_inc(v_snd_2607_);
lean_inc(v_fst_2606_);
lean_dec(v_b_2597_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2626_;
state = 1; continue;
}
} else {
let mut v_a_2627_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2629_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2630_: u8 = 0; let mut v_isSharedCheck_2634_: u8 = 0; 
lean_dec(v_a_2603_);
lean_dec_ref(v_b_2597_);
v_a_2627_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2634_ = (!lean_is_exclusive(v___x_2604_)) as u8;
if v_isSharedCheck_2634_ == 0 {
v___x_2629_ = v___x_2604_;
v_isShared_2630_ = v_isSharedCheck_2634_;
state = 4; continue;
} else {
lean_inc(v_a_2627_);
lean_dec(v___x_2604_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
state = 4; continue;
}
}
} else {
let mut v_a_2635_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2637_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2638_: u8 = 0; let mut v_isSharedCheck_2642_: u8 = 0; 
lean_dec_ref(v_b_2597_);
v_a_2635_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2642_ = (!lean_is_exclusive(v___x_2602_)) as u8;
if v_isSharedCheck_2642_ == 0 {
v___x_2637_ = v___x_2602_;
v_isShared_2638_ = v_isSharedCheck_2642_;
state = 6; continue;
} else {
lean_inc(v_a_2635_);
lean_dec(v___x_2602_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
state = 6; continue;
}
}
}
}
1 => {
v___x_2611_ = lean_unbox_float(v_a_2603_);
lean_dec(v_a_2603_);
v___x_2612_ = lean_unbox_float(v_a_2605_);
lean_dec(v_a_2605_);
v___x_2613_ = lean_float_decLt(v___x_2611_, v___x_2612_);
if v___x_2613_ == 0 {
let mut v___x_2614_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2615_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2617_: *mut lean_object = core::ptr::null_mut(); 
v___x_2614_ = lean_unsigned_to_nat(1);
v___x_2615_ = lean_nat_add(v_snd_2607_, v___x_2614_);
lean_dec(v_snd_2607_);
if v_isShared_2610_ == 0 {
lean_ctor_set(v___x_2609_, 1, v___x_2615_);
v___x_2617_ = v___x_2609_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2619_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_fst_2606_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2619_;
state = 2; continue;
}
} else {
let mut v___x_2620_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2623_: *mut lean_object = core::ptr::null_mut(); 
v___x_2620_ = lean_unsigned_to_nat(1);
v___x_2621_ = lean_nat_add(v_fst_2606_, v___x_2620_);
lean_dec(v_fst_2606_);
if v_isShared_2610_ == 0 {
lean_ctor_set(v___x_2609_, 0, v___x_2621_);
v___x_2623_ = v___x_2609_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_2625_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_snd_2607_);
v___x_2623_ = v_reuseFailAlloc_2625_;
state = 3; continue;
}
}
}
4 => {
if v_isShared_2630_ == 0 {
v___x_2632_ = v___x_2629_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_2633_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
state = 5; continue;
}
}
6 => {
if v_isShared_2638_ == 0 {
v___x_2640_ = v___x_2637_;
state = 7; continue;
} else {
let mut v_reuseFailAlloc_2641_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
state = 7; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00compareAnyBench_spec__0___redArg___boxed(mut v_as_x27_2643_: *mut lean_object, mut v_b_2644_: *mut lean_object, mut v___y_2645_: *mut lean_object) -> *mut lean_object{
let mut v_res_2646_: *mut lean_object = core::ptr::null_mut(); 
v_res_2646_ = l_List_forIn_x27_loop___at___00compareAnyBench_spec__0___redArg(v_as_x27_2643_, v_b_2644_);
lean_dec(v_as_x27_2643_);
return v_res_2646_;
}
#[no_mangle] pub unsafe extern "C" fn l_compareAnyBench() -> *mut lean_object{
let mut v___x_2648_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2649_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2650_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2651_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2653_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2656_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2659_: *mut lean_object = core::ptr::null_mut(); let mut v_inputSizes_2660_: *mut lean_object = core::ptr::null_mut(); let mut v_nativeBetter_2661_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2662_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2663_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2664_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_2665_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_2666_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2667_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2668_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2669_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2670_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2671_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2673_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2674_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2675_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2677_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2678_: u8 = 0; let mut v___x_2680_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2681_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2682_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_2648_ = lean_unsigned_to_nat(100);
v___x_2649_ = lean_unsigned_to_nat(500);
v___x_2650_ = lean_unsigned_to_nat(1000);
v___x_2651_ = lean_unsigned_to_nat(5000);
v___x_2652_ = lean_unsigned_to_nat(10000);
v___x_2653_ = lean_unsigned_to_nat(100000);
v___x_2654_ = lean_box(0);
v___x_2655_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2656_, 0, v___x_2652_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2657_, 0, v___x_2651_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2658_, 0, v___x_2650_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2659_, 0, v___x_2649_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v_inputSizes_2660_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_inputSizes_2660_, 0, v___x_2648_);
lean_ctor_set(v_inputSizes_2660_, 1, v___x_2659_);
v_nativeBetter_2661_ = lean_unsigned_to_nat(0);
v___x_2662_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2662_, 0, v_nativeBetter_2661_);
lean_ctor_set(v___x_2662_, 1, v_nativeBetter_2661_);
v___x_2663_ = l_List_forIn_x27_loop___at___00compareAnyBench_spec__0___redArg(v_inputSizes_2660_, v___x_2662_);
lean_dec_ref_known(v_inputSizes_2660_, 2);
if lean_obj_tag(v___x_2663_) == 0 {
let mut v_a_2664_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_2665_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_2666_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2667_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2668_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2669_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2670_: *mut lean_object = core::ptr::null_mut(); 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
v_fst_2665_ = lean_ctor_get(v_a_2664_, 0);
lean_inc(v_fst_2665_);
v_snd_2666_ = lean_ctor_get(v_a_2664_, 1);
lean_inc(v_snd_2666_);
lean_dec(v_a_2664_);
v___x_2667_ = lean_mk_string_unchecked(b""Native function better: "\0".as_ptr().cast(), 24, 24);
v___x_2668_ = l_Nat_reprFast(v_fst_2665_);
v___x_2669_ = lean_string_append(v___x_2667_, v___x_2668_);
lean_dec_ref(v___x_2668_);
v___x_2670_ = l_IO_println___at___00compareAnyBench_spec__1(v___x_2669_);
if lean_obj_tag(v___x_2670_) == 0 {
let mut v___x_2671_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2673_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2674_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_2670_, 1);
v___x_2671_ = lean_mk_string_unchecked(b""Iterator function better: "\0".as_ptr().cast(), 26, 26);
v___x_2672_ = l_Nat_reprFast(v_snd_2666_);
v___x_2673_ = lean_string_append(v___x_2671_, v___x_2672_);
lean_dec_ref(v___x_2672_);
v___x_2674_ = l_IO_println___at___00compareAnyBench_spec__1(v___x_2673_);
return v___x_2674_;
} else {
lean_dec(v_snd_2666_);
return v___x_2670_;
}
} else {
let mut v_a_2675_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2677_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2678_: u8 = 0; let mut v_isSharedCheck_2682_: u8 = 0; 
v_a_2675_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2682_ = (!lean_is_exclusive(v___x_2663_)) as u8;
if v_isSharedCheck_2682_ == 0 {
v___x_2677_ = v___x_2663_;
v_isShared_2678_ = v_isSharedCheck_2682_;
state = 1; continue;
} else {
lean_inc(v_a_2675_);
lean_dec(v___x_2663_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
state = 1; continue;
}
}
}
1 => {
if v_isShared_2678_ == 0 {
v___x_2680_ = v___x_2677_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2681_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_compareAnyBench___boxed(mut v_a_2683_: *mut lean_object) -> *mut lean_object{
let mut v_res_2684_: *mut lean_object = core::ptr::null_mut(); 
v_res_2684_ = l_compareAnyBench();
return v_res_2684_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00compareAnyBench_spec__0(mut v_as_2685_: *mut lean_object, mut v_as_x27_2686_: *mut lean_object, mut v_b_2687_: *mut lean_object, mut v_a_2688_: *mut lean_object) -> *mut lean_object{
let mut v___x_2690_: *mut lean_object = core::ptr::null_mut(); 
v___x_2690_ = l_List_forIn_x27_loop___at___00compareAnyBench_spec__0___redArg(v_as_x27_2686_, v_b_2687_);
return v___x_2690_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00compareAnyBench_spec__0___boxed(mut v_as_2691_: *mut lean_object, mut v_as_x27_2692_: *mut lean_object, mut v_b_2693_: *mut lean_object, mut v_a_2694_: *mut lean_object, mut v___y_2695_: *mut lean_object) -> *mut lean_object{
let mut v_res_2696_: *mut lean_object = core::ptr::null_mut(); 
v_res_2696_ = l_List_forIn_x27_loop___at___00compareAnyBench_spec__0(v_as_2691_, v_as_x27_2692_, v_b_2693_, v_a_2694_);
lean_dec(v_as_x27_2692_);
lean_dec(v_as_2691_);
return v_res_2696_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00main_spec__0(mut v_msg_2697_: *mut lean_object) -> *mut lean_object{
let mut v___x_2699_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2700_: *mut lean_object = core::ptr::null_mut(); let mut v___x_727__overap_2701_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2702_: *mut lean_object = core::ptr::null_mut(); 
v___x_2699_ = l_instInhabitedError;
v___x_2700_ = lean_alloc_closure(l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___x_2700_, 0, lean_box(0));
lean_closure_set(v___x_2700_, 1, lean_box(0));
lean_closure_set(v___x_2700_, 2, v___x_2699_);
v___x_727__overap_2701_ = lean_panic_fn_borrowed(v___x_2700_, v_msg_2697_);
lean_dec_ref(v___x_2700_);
v___x_2702_ = lean_apply_1(v___x_727__overap_2701_, lean_box(0));
return v___x_2702_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00main_spec__0___boxed(mut v_msg_2703_: *mut lean_object, mut v___y_2704_: *mut lean_object) -> *mut lean_object{
let mut v_res_2705_: *mut lean_object = core::ptr::null_mut(); 
v_res_2705_ = l_panic___at___00main_spec__0(v_msg_2703_);
return v_res_2705_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00main_spec__1___redArg(mut v_seed_2706_: u64, mut v_size_2707_: *mut lean_object, mut v_as_x27_2708_: *mut lean_object, mut v_b_2709_: *mut lean_object) -> *mut lean_object{
let mut v___x_2711_: *mut lean_object = core::ptr::null_mut(); let mut v_head_2712_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2713_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_2714_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_2715_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2716_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2717_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2718_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2719_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2720_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2721_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2722_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2723_: f64 = 0.0; let mut v___x_2724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2725_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2727_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2728_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2729_: *mut lean_object = core::ptr::null_mut(); let mut v_a_2731_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2733_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2734_: u8 = 0; let mut v___x_2736_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2737_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2738_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_as_x27_2708_) == 0 {
let mut v___x_2711_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_size_2707_);
v___x_2711_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_2711_, 0, v_b_2709_);
return v___x_2711_;
} else {
let mut v_head_2712_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_2713_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_2714_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_2715_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2716_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2717_: *mut lean_object = core::ptr::null_mut(); 
v_head_2712_ = lean_ctor_get(v_as_x27_2708_, 0);
v_tail_2713_ = lean_ctor_get(v_as_x27_2708_, 1);
v_fst_2714_ = lean_ctor_get(v_head_2712_, 0);
v_snd_2715_ = lean_ctor_get(v_head_2712_, 1);
v___x_2716_ = lean_box_uint64(v_seed_2706_);
lean_inc(v_snd_2715_);
lean_inc(v_size_2707_);
v___x_2717_ = lean_apply_3(v_snd_2715_, v___x_2716_, v_size_2707_, lean_box(0));
if lean_obj_tag(v___x_2717_) == 0 {
let mut v_a_2718_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2719_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2720_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2721_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2722_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2723_: f64 = 0.0; let mut v___x_2724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2725_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2727_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2728_: *mut lean_object = core::ptr::null_mut(); 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = lean_mk_string_unchecked(b""measurement: "\0".as_ptr().cast(), 13, 13);
v___x_2720_ = lean_string_append(v___x_2719_, v_fst_2714_);
v___x_2721_ = lean_mk_string_unchecked(b"" "\0".as_ptr().cast(), 1, 1);
v___x_2722_ = lean_string_append(v___x_2720_, v___x_2721_);
lean_dec_ref(v___x_2721_);
v___x_2723_ = lean_unbox_float(v_a_2718_);
lean_dec(v_a_2718_);
v___x_2724_ = lean_float_to_string(v___x_2723_);
v___x_2725_ = lean_string_append(v___x_2722_, v___x_2724_);
lean_dec_ref(v___x_2724_);
v___x_2726_ = lean_mk_string_unchecked(b"" s"\0".as_ptr().cast(), 2, 2);
v___x_2727_ = lean_string_append(v___x_2725_, v___x_2726_);
lean_dec_ref(v___x_2726_);
v___x_2728_ = l_IO_println___at___00compareAnyBench_spec__1(v___x_2727_);
if lean_obj_tag(v___x_2728_) == 0 {
let mut v___x_2729_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_2728_, 1);
v___x_2729_ = lean_box(0);
v_as_x27_2708_ = v_tail_2713_;
v_b_2709_ = v___x_2729_;
state = 0; continue;
} else {
lean_dec(v_size_2707_);
return v___x_2728_;
}
} else {
let mut v_a_2731_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2733_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2734_: u8 = 0; let mut v_isSharedCheck_2738_: u8 = 0; 
lean_dec(v_size_2707_);
v_a_2731_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2738_ = (!lean_is_exclusive(v___x_2717_)) as u8;
if v_isSharedCheck_2738_ == 0 {
v___x_2733_ = v___x_2717_;
v_isShared_2734_ = v_isSharedCheck_2738_;
state = 1; continue;
} else {
lean_inc(v_a_2731_);
lean_dec(v___x_2717_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
state = 1; continue;
}
}
}
}
1 => {
if v_isShared_2734_ == 0 {
v___x_2736_ = v___x_2733_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2737_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(mut v_seed_2739_: *mut lean_object, mut v_size_2740_: *mut lean_object, mut v_as_x27_2741_: *mut lean_object, mut v_b_2742_: *mut lean_object, mut v___y_2743_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_2744_: u64 = 0; let mut v_res_2745_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_2744_ = lean_unbox_uint64(v_seed_2739_);
lean_dec_ref(v_seed_2739_);
v_res_2745_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_seed_boxed_2744_, v_size_2740_, v_as_x27_2741_, v_b_2742_);
lean_dec(v_as_x27_2741_);
return v_res_2745_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_args_2746_: *mut lean_object) -> *mut lean_object{
let mut v___x_2748_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2749_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2750_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2751_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2752_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2753_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2754_: *mut lean_object = core::ptr::null_mut(); let mut v_size_2755_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2756_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2757_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2758_: u8 = 0; let mut v___x_2759_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2760_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2761_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2762_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2763_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2764_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2766_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2767_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2768_: *mut lean_object = core::ptr::null_mut(); let mut v_seed_2769_: u64 = 0; let mut v___x_2770_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2771_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2772_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2773_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2775_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2776_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2777_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2778_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2779_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2780_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2781_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2782_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2783_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2784_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2785_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2786_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2787_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2789_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2790_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2791_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2792_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2793_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2794_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2795_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2796_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2797_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2798_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2799_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2800_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2801_: *mut lean_object = core::ptr::null_mut(); let mut v_benches_2802_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2803_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2804_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2806_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2807_: u8 = 0; let mut v___x_2809_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2810_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2811_: u8 = 0; let mut v_unused_2812_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_2748_ = lean_mk_string_unchecked(b"""\0".as_ptr().cast(), 0, 0);
v___x_2749_ = lean_unsigned_to_nat(0);
v___x_2750_ = l_List_get_x21Internal___redArg(v___x_2748_, v_args_2746_, v___x_2749_);
v___x_2751_ = lean_unsigned_to_nat(1);
v___x_2752_ = l_List_get_x21Internal___redArg(v___x_2748_, v_args_2746_, v___x_2751_);
lean_dec(v_args_2746_);
lean_dec_ref(v___x_2748_);
v___x_2753_ = lean_string_utf8_byte_size(v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2749_);
lean_ctor_set(v___x_2754_, 2, v___x_2753_);
v_size_2755_ = l_String_Slice_toNat_x21(v___x_2754_);
lean_dec_ref_known(v___x_2754_, 3);
v___x_2756_ = lean_unsigned_to_nat(100);
v___x_2757_ = lean_nat_mod(v_size_2755_, v___x_2756_);
v___x_2758_ = lean_nat_dec_eq(v___x_2757_, v___x_2749_);
lean_dec(v___x_2757_);
if v___x_2758_ == 0 {
let mut v___x_2759_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2760_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2761_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2762_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2763_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2764_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2765_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_size_2755_);
lean_dec(v___x_2750_);
v___x_2759_ = lean_mk_string_unchecked(b""hashmap"\0".as_ptr().cast(), 7, 7);
v___x_2760_ = lean_mk_string_unchecked(b""main"\0".as_ptr().cast(), 4, 4);
v___x_2761_ = lean_unsigned_to_nat(270);
v___x_2762_ = lean_unsigned_to_nat(2);
v___x_2763_ = lean_mk_string_unchecked(b""assertion violation: size % REP == 0\n  "\0".as_ptr().cast(), 39, 39);
v___x_2764_ = l_mkPanicMessageWithDecl(v___x_2759_, v___x_2760_, v___x_2761_, v___x_2762_, v___x_2763_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2760_);
lean_dec_ref(v___x_2759_);
v___x_2765_ = l_panic___at___00main_spec__0(v___x_2764_);
return v___x_2765_;
} else {
let mut v___x_2766_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2767_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2768_: *mut lean_object = core::ptr::null_mut(); let mut v_seed_2769_: u64 = 0; let mut v___x_2770_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2771_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2772_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2773_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2775_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2776_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2777_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2778_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2779_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2780_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2781_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2782_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2783_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2784_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2785_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2786_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2787_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2789_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2790_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2791_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2792_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2793_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2794_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2795_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2796_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2797_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2798_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2799_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2800_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2801_: *mut lean_object = core::ptr::null_mut(); let mut v_benches_2802_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2803_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2804_: *mut lean_object = core::ptr::null_mut(); 
v___x_2766_ = lean_string_utf8_byte_size(v___x_2750_);
v___x_2767_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_2767_, 0, v___x_2750_);
lean_ctor_set(v___x_2767_, 1, v___x_2749_);
lean_ctor_set(v___x_2767_, 2, v___x_2766_);
v___x_2768_ = l_String_Slice_toNat_x21(v___x_2767_);
lean_dec_ref_known(v___x_2767_, 3);
v_seed_2769_ = lean_uint64_of_nat(v___x_2768_);
lean_dec(v___x_2768_);
v___x_2770_ = lean_mk_string_unchecked(b""containsHit"\0".as_ptr().cast(), 11, 11);
v___x_2771_ = lean_alloc_closure(l_benchContainsHit___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2772_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2772_, 0, v___x_2770_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = lean_mk_string_unchecked(b""containsMiss"\0".as_ptr().cast(), 12, 12);
v___x_2774_ = lean_alloc_closure(l_benchContainsMiss___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2775_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = lean_mk_string_unchecked(b""iterate"\0".as_ptr().cast(), 7, 7);
v___x_2777_ = lean_alloc_closure(l_benchIterate___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2778_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = lean_mk_string_unchecked(b""insertIfNewHit"\0".as_ptr().cast(), 14, 14);
v___x_2780_ = lean_alloc_closure(l_benchInsertIfNewHit___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2781_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = lean_mk_string_unchecked(b""insertHit"\0".as_ptr().cast(), 9, 9);
v___x_2783_ = lean_alloc_closure(l_benchInsertHit___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2784_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2784_, 0, v___x_2782_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = lean_mk_string_unchecked(b""insertMissEmpty"\0".as_ptr().cast(), 15, 15);
v___x_2786_ = lean_alloc_closure(l_benchInsertMissEmpty___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2787_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2787_, 0, v___x_2785_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = lean_mk_string_unchecked(b""insertMissEmptyWithCapacity"\0".as_ptr().cast(), 27, 27);
v___x_2789_ = lean_alloc_closure(l_benchInsertMissEmptyWithCapacity___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2790_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_mk_string_unchecked(b""eraseInsert"\0".as_ptr().cast(), 11, 11);
v___x_2792_ = lean_alloc_closure(l_benchEraseInsert___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2793_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2796_, 0, v___x_2790_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2797_, 0, v___x_2787_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2798_, 0, v___x_2784_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2799_, 0, v___x_2781_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2800_, 0, v___x_2778_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2801_, 0, v___x_2775_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v_benches_2802_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_benches_2802_, 0, v___x_2772_);
lean_ctor_set(v_benches_2802_, 1, v___x_2801_);
v___x_2803_ = lean_box(0);
v___x_2804_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_seed_2769_, v_size_2755_, v_benches_2802_, v___x_2803_);
lean_dec_ref_known(v_benches_2802_, 2);
if lean_obj_tag(v___x_2804_) == 0 {
let mut v___x_2806_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2807_: u8 = 0; let mut v_isSharedCheck_2811_: u8 = 0; 
v_isSharedCheck_2811_ = (!lean_is_exclusive(v___x_2804_)) as u8;
if v_isSharedCheck_2811_ == 0 {
let mut v_unused_2812_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2812_ = lean_ctor_get(v___x_2804_, 0);
lean_dec(v_unused_2812_);
v___x_2806_ = v___x_2804_;
v_isShared_2807_ = v_isSharedCheck_2811_;
state = 1; continue;
} else {
lean_dec(v___x_2804_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
state = 1; continue;
}
} else {
return v___x_2804_;
}
}
}
1 => {
if v_isShared_2807_ == 0 {
lean_ctor_set(v___x_2806_, 0, v___x_2803_);
v___x_2809_ = v___x_2806_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2810_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2803_);
v___x_2809_ = v_reuseFailAlloc_2810_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_args_2813_: *mut lean_object, mut v_a_2814_: *mut lean_object) -> *mut lean_object{
let mut v_res_2815_: *mut lean_object = core::ptr::null_mut(); 
v_res_2815_ = _lean_main(v_args_2813_);
return v_res_2815_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00main_spec__1(mut v_seed_2816_: u64, mut v_size_2817_: *mut lean_object, mut v_as_2818_: *mut lean_object, mut v_as_x27_2819_: *mut lean_object, mut v_b_2820_: *mut lean_object, mut v_a_2821_: *mut lean_object) -> *mut lean_object{
let mut v___x_2823_: *mut lean_object = core::ptr::null_mut(); 
v___x_2823_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_seed_2816_, v_size_2817_, v_as_x27_2819_, v_b_2820_);
return v___x_2823_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00main_spec__1___boxed(mut v_seed_2824_: *mut lean_object, mut v_size_2825_: *mut lean_object, mut v_as_2826_: *mut lean_object, mut v_as_x27_2827_: *mut lean_object, mut v_b_2828_: *mut lean_object, mut v_a_2829_: *mut lean_object, mut v___y_2830_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_2831_: u64 = 0; let mut v_res_2832_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_2831_ = lean_unbox_uint64(v_seed_2824_);
lean_dec_ref(v_seed_2824_);
v_res_2832_ = l_List_forIn_x27_loop___at___00main_spec__1(v_seed_boxed_2831_, v_size_2825_, v_as_2826_, v_as_x27_2827_, v_b_2828_, v_a_2829_);
lean_dec(v_as_x27_2827_);
lean_dec(v_as_2826_);
return v_res_2832_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Data_HashMap(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Data_Iterators(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Data_HashSet(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Data_HashSet_Iterator(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_hashmap(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Data_Iterators(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Data_HashSet(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Iterator(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_REP = _init_l_REP();
lean_mark_persistent(l_REP);
l_testPrimes = _init_l_testPrimes();
lean_mark_persistent(l_testPrimes);
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
  let res = initialize_hashmap(1 /* builtin */);
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
