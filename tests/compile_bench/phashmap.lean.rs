// Lean compiler output
// Module: phashmap
// Imports: public import Init public meta import Init public import Lean.Data.PersistentHashMap public import Std.Data.Iterators
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Lean_PersistentHashMap_mkEmptyEntriesArray(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_uint64_add(_: u64, _: u64) -> u64;
    fn lean_uint64_mul(_: u64, _: u64) -> u64;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_to_usize(_: u64) -> usize;
    fn lean_usize_shift_left(_: usize, _: usize) -> usize;
    fn lean_usize_sub(_: usize, _: usize) -> usize;
    fn lean_usize_land(_: usize, _: usize) -> usize;
    fn lean_usize_to_nat(_: usize) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_fget(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fset(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_dec_eq(_: u64, _: u64) -> u8;
    fn l_Lean_PersistentHashMap_mkCollisionNode___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_usize_shift_right(_: usize, _: usize) -> usize;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fget_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_PersistentHashMap_mkEmptyEntries(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_usize_mul(_: usize, _: usize) -> usize;
    fn lean_usize_dec_le(_: usize, _: usize) -> u8;
    fn l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mul(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_borrowed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_io_mono_nanos_now() -> *mut lean_object;
    fn lean_float_of_nat(_: *mut lean_object) -> f64;
    fn lean_float_div(_: f64, _: f64) -> f64;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_PersistentHashMap_Node_isEmpty___redArg(_: *mut lean_object) -> u8;
    fn lean_array_get(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_set(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_PersistentHashMap_isUnaryNode___redArg(_: *mut lean_object) -> *mut lean_object;
    fn l_Array_eraseIdx___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_usize_of_nat(_: *mut lean_object) -> usize;
    fn lean_usize_dec_eq(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_float_to_string(_: f64) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn l_List_get_x21Internal___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_mkPanicMessageWithDecl(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    static mut l_instInhabitedError: *mut lean_object;
    fn l_instInhabitedEIO___aux__1___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_panic_fn_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint64_of_nat(_: *mut lean_object) -> u64;
}
#[no_mangle] pub static mut l_REP: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___boxed__const__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*0 + 8) as u16, m_other: 0, m_tag: 0 }, m_objs: [0 as *mut lean_object] };
#[no_mangle] pub static mut l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___boxed__const__1: *mut lean_object = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___boxed__const__1_value) as *mut lean_object;
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
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_empty___at___00mkMapWithCap_spec__1(mut v_00_u03b2_37_: *mut lean_object) -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); 
v___x_38_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
v___x_39_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2_spec__4___redArg(mut v_x_40_: *mut lean_object, mut v_x_41_: *mut lean_object, mut v_x_42_: u64, mut v_x_43_: *mut lean_object) -> *mut lean_object{
let mut v_ks_44_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_48_: u8 = 0; let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: u8 = 0; let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_56_: *mut lean_object = core::ptr::null_mut(); let mut v_k_x27_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: u64 = 0; let mut v___x_59_: u8 = 0; let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_71_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_72_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_ks_44_ = lean_ctor_get(v_x_40_, 0);
v_vs_45_ = lean_ctor_get(v_x_40_, 1);
v_isSharedCheck_72_ = (!lean_is_exclusive(v_x_40_)) as u8;
if v_isSharedCheck_72_ == 0 {
v___x_47_ = v_x_40_;
v_isShared_48_ = v_isSharedCheck_72_;
state = 1; continue;
} else {
lean_inc(v_vs_45_);
lean_inc(v_ks_44_);
lean_dec(v_x_40_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_72_;
state = 1; continue;
}
}
1 => {
v___x_49_ = lean_array_get_size(v_ks_44_);
v___x_50_ = lean_nat_dec_lt(v_x_41_, v___x_49_);
if v___x_50_ == 0 {
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_41_);
v___x_51_ = lean_box_uint64(v_x_42_);
v___x_52_ = lean_array_push(v_ks_44_, v___x_51_);
v___x_53_ = lean_array_push(v_vs_45_, v_x_43_);
if v_isShared_48_ == 0 {
lean_ctor_set(v___x_47_, 1, v___x_53_);
lean_ctor_set(v___x_47_, 0, v___x_52_);
v___x_55_ = v___x_47_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_56_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
state = 2; continue;
}
} else {
let mut v_k_x27_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: u64 = 0; let mut v___x_59_: u8 = 0; 
v_k_x27_57_ = lean_array_fget_borrowed(v_ks_44_, v_x_41_);
v___x_58_ = lean_unbox_uint64(v_k_x27_57_);
v___x_59_ = lean_uint64_dec_eq(v_x_42_, v___x_58_);
if v___x_59_ == 0 {
let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_48_ == 0 {
v___x_61_ = v___x_47_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_65_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_ks_44_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_vs_45_);
v___x_61_ = v_reuseFailAlloc_65_;
state = 3; continue;
}
} else {
let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); 
v___x_66_ = lean_box_uint64(v_x_42_);
v___x_67_ = lean_array_fset(v_ks_44_, v_x_41_, v___x_66_);
v___x_68_ = lean_array_fset(v_vs_45_, v_x_41_, v_x_43_);
lean_dec(v_x_41_);
if v_isShared_48_ == 0 {
lean_ctor_set(v___x_47_, 1, v___x_68_);
lean_ctor_set(v___x_47_, 0, v___x_67_);
v___x_70_ = v___x_47_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_71_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
state = 4; continue;
}
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2_spec__4___redArg___boxed(mut v_x_73_: *mut lean_object, mut v_x_74_: *mut lean_object, mut v_x_75_: *mut lean_object, mut v_x_76_: *mut lean_object) -> *mut lean_object{
let mut v_x_1223__boxed_77_: u64 = 0; let mut v_res_78_: *mut lean_object = core::ptr::null_mut(); 
v_x_1223__boxed_77_ = lean_unbox_uint64(v_x_75_);
lean_dec_ref(v_x_75_);
v_res_78_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2_spec__4___redArg(v_x_73_, v_x_74_, v_x_1223__boxed_77_, v_x_76_);
return v_res_78_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2___redArg(mut v_n_79_: *mut lean_object, mut v_k_80_: u64, mut v_v_81_: *mut lean_object) -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = lean_unsigned_to_nat(0);
v___x_83_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2_spec__4___redArg(v_n_79_, v___x_82_, v_k_80_, v_v_81_);
return v___x_83_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2___redArg___boxed(mut v_n_84_: *mut lean_object, mut v_k_85_: *mut lean_object, mut v_v_86_: *mut lean_object) -> *mut lean_object{
let mut v_k_boxed_87_: u64 = 0; let mut v_res_88_: *mut lean_object = core::ptr::null_mut(); 
v_k_boxed_87_ = lean_unbox_uint64(v_k_85_);
lean_dec_ref(v_k_85_);
v_res_88_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2___redArg(v_n_84_, v_k_boxed_87_, v_v_86_);
return v_res_88_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(mut v_x_89_: *mut lean_object, mut v_x_90_: usize, mut v_x_91_: usize, mut v_x_92_: u64, mut v_x_93_: *mut lean_object) -> *mut lean_object{
let mut v_es_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: usize = 0; let mut v___x_96_: usize = 0; let mut v___x_97_: usize = 0; let mut v___x_98_: usize = 0; let mut v___x_99_: usize = 0; let mut v_j_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: u8 = 0; let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_105_: u8 = 0; let mut v_v_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v_xs_x27_108_: *mut lean_object = core::ptr::null_mut(); let mut v___y_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_114_: *mut lean_object = core::ptr::null_mut(); let mut v_key_115_: *mut lean_object = core::ptr::null_mut(); let mut v_val_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_119_: u8 = 0; let mut v___x_120_: u64 = 0; let mut v___x_121_: u8 = 0; let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_128_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_129_: u8 = 0; let mut v_node_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_133_: u8 = 0; let mut v___x_134_: usize = 0; let mut v___x_135_: usize = 0; let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_139_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_140_: u8 = 0; let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_143_: u8 = 0; let mut v_unused_144_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_145_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_149_: u8 = 0; let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v_newNode_152_: *mut lean_object = core::ptr::null_mut(); let mut v___y_154_: u8 = 0; let mut v_ks_155_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_156_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: usize = 0; let mut v___x_161_: u8 = 0; let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: u8 = 0; let mut v_reuseFailAlloc_165_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_166_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_89_) == 0 {
let mut v_es_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: usize = 0; let mut v___x_96_: usize = 0; let mut v___x_97_: usize = 0; let mut v___x_98_: usize = 0; let mut v___x_99_: usize = 0; let mut v_j_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: u8 = 0; 
v_es_94_ = lean_ctor_get(v_x_89_, 0);
v___x_95_ = 5usize;
v___x_96_ = 1usize;
v___x_97_ = lean_usize_shift_left(v___x_96_, v___x_95_);
v___x_98_ = lean_usize_sub(v___x_97_, v___x_96_);
v___x_99_ = lean_usize_land(v_x_90_, v___x_98_);
v_j_100_ = lean_usize_to_nat(v___x_99_);
v___x_101_ = lean_array_get_size(v_es_94_);
v___x_102_ = lean_nat_dec_lt(v_j_100_, v___x_101_);
if v___x_102_ == 0 {
lean_dec(v_j_100_);
lean_dec(v_x_93_);
return v_x_89_;
} else {
let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_105_: u8 = 0; let mut v_isSharedCheck_143_: u8 = 0; 
lean_inc_ref(v_es_94_);
v_isSharedCheck_143_ = (!lean_is_exclusive(v_x_89_)) as u8;
if v_isSharedCheck_143_ == 0 {
let mut v_unused_144_: *mut lean_object = core::ptr::null_mut(); 
v_unused_144_ = lean_ctor_get(v_x_89_, 0);
lean_dec(v_unused_144_);
v___x_104_ = v_x_89_;
v_isShared_105_ = v_isSharedCheck_143_;
state = 1; continue;
} else {
lean_dec(v_x_89_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_143_;
state = 1; continue;
}
}
} else {
let mut v_ks_145_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_149_: u8 = 0; let mut v_isSharedCheck_166_: u8 = 0; 
v_ks_145_ = lean_ctor_get(v_x_89_, 0);
v_vs_146_ = lean_ctor_get(v_x_89_, 1);
v_isSharedCheck_166_ = (!lean_is_exclusive(v_x_89_)) as u8;
if v_isSharedCheck_166_ == 0 {
v___x_148_ = v_x_89_;
v_isShared_149_ = v_isSharedCheck_166_;
state = 8; continue;
} else {
lean_inc(v_vs_146_);
lean_inc(v_ks_145_);
lean_dec(v_x_89_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_166_;
state = 8; continue;
}
}
}
1 => {
v_v_106_ = lean_array_fget(v_es_94_, v_j_100_);
v___x_107_ = lean_box(0);
v_xs_x27_108_ = lean_array_fset(v_es_94_, v_j_100_, v___x_107_);
match lean_obj_tag(v_v_106_)
{
0 => {
let mut v_key_115_: *mut lean_object = core::ptr::null_mut(); let mut v_val_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_119_: u8 = 0; let mut v_isSharedCheck_129_: u8 = 0; 
v_key_115_ = lean_ctor_get(v_v_106_, 0);
v_val_116_ = lean_ctor_get(v_v_106_, 1);
v_isSharedCheck_129_ = (!lean_is_exclusive(v_v_106_)) as u8;
if v_isSharedCheck_129_ == 0 {
v___x_118_ = v_v_106_;
v_isShared_119_ = v_isSharedCheck_129_;
state = 4; continue;
} else {
lean_inc(v_val_116_);
lean_inc(v_key_115_);
lean_dec(v_v_106_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_129_;
state = 4; continue;
}
}
1 => {
let mut v_node_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_133_: u8 = 0; let mut v_isSharedCheck_140_: u8 = 0; 
v_node_130_ = lean_ctor_get(v_v_106_, 0);
v_isSharedCheck_140_ = (!lean_is_exclusive(v_v_106_)) as u8;
if v_isSharedCheck_140_ == 0 {
v___x_132_ = v_v_106_;
v_isShared_133_ = v_isSharedCheck_140_;
state = 6; continue;
} else {
lean_inc(v_node_130_);
lean_dec(v_v_106_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_140_;
state = 6; continue;
}
}
_ => {
let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); 
v___x_141_ = lean_box_uint64(v_x_92_);
v___x_142_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v_x_93_);
v___y_110_ = v___x_142_;
state = 2; continue;
}
}
}
8 => {
if v_isShared_149_ == 0 {
v___x_151_ = v___x_148_;
state = 9; continue;
} else {
let mut v_reuseFailAlloc_165_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_ks_145_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_vs_146_);
v___x_151_ = v_reuseFailAlloc_165_;
state = 9; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__3___redArg(mut v_depth_167_: usize, mut v_keys_168_: *mut lean_object, mut v_vals_169_: *mut lean_object, mut v_i_170_: *mut lean_object, mut v_entries_171_: *mut lean_object) -> *mut lean_object{
let mut v___x_172_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: u8 = 0; let mut v_k_174_: *mut lean_object = core::ptr::null_mut(); let mut v_v_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: u64 = 0; let mut v_h_177_: usize = 0; let mut v___x_178_: usize = 0; let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_180_: usize = 0; let mut v___x_181_: usize = 0; let mut v___x_182_: usize = 0; let mut v_h_183_: usize = 0; let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: u64 = 0; let mut v___x_186_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_172_ = lean_array_get_size(v_keys_168_);
v___x_173_ = lean_nat_dec_lt(v_i_170_, v___x_172_);
if v___x_173_ == 0 {
lean_dec(v_i_170_);
return v_entries_171_;
} else {
let mut v_k_174_: *mut lean_object = core::ptr::null_mut(); let mut v_v_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: u64 = 0; let mut v_h_177_: usize = 0; let mut v___x_178_: usize = 0; let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_180_: usize = 0; let mut v___x_181_: usize = 0; let mut v___x_182_: usize = 0; let mut v_h_183_: usize = 0; let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: u64 = 0; let mut v___x_186_: *mut lean_object = core::ptr::null_mut(); 
v_k_174_ = lean_array_fget_borrowed(v_keys_168_, v_i_170_);
v_v_175_ = lean_array_fget_borrowed(v_vals_169_, v_i_170_);
v___x_176_ = lean_unbox_uint64(v_k_174_);
v_h_177_ = lean_uint64_to_usize(v___x_176_);
v___x_178_ = 5usize;
v___x_179_ = lean_unsigned_to_nat(1);
v___x_180_ = 1usize;
v___x_181_ = lean_usize_sub(v_depth_167_, v___x_180_);
v___x_182_ = lean_usize_mul(v___x_178_, v___x_181_);
v_h_183_ = lean_usize_shift_right(v_h_177_, v___x_182_);
v___x_184_ = lean_nat_add(v_i_170_, v___x_179_);
lean_dec(v_i_170_);
v___x_185_ = lean_unbox_uint64(v_k_174_);
lean_inc(v_v_175_);
v___x_186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_entries_171_, v_h_183_, v_depth_167_, v___x_185_, v_v_175_);
v_i_170_ = v___x_184_;
v_entries_171_ = v___x_186_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__3___redArg___boxed(mut v_depth_188_: *mut lean_object, mut v_keys_189_: *mut lean_object, mut v_vals_190_: *mut lean_object, mut v_i_191_: *mut lean_object, mut v_entries_192_: *mut lean_object) -> *mut lean_object{
let mut v_depth_boxed_193_: usize = 0; let mut v_res_194_: *mut lean_object = core::ptr::null_mut(); 
v_depth_boxed_193_ = lean_unbox_usize(v_depth_188_);
lean_dec(v_depth_188_);
v_res_194_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__3___redArg(v_depth_boxed_193_, v_keys_189_, v_vals_190_, v_i_191_, v_entries_192_);
lean_dec_ref(v_vals_190_);
lean_dec_ref(v_keys_189_);
return v_res_194_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0___redArg___boxed(mut v_x_195_: *mut lean_object, mut v_x_196_: *mut lean_object, mut v_x_197_: *mut lean_object, mut v_x_198_: *mut lean_object, mut v_x_199_: *mut lean_object) -> *mut lean_object{
let mut v_x_1305__boxed_200_: usize = 0; let mut v_x_1306__boxed_201_: usize = 0; let mut v_x_1307__boxed_202_: u64 = 0; let mut v_res_203_: *mut lean_object = core::ptr::null_mut(); 
v_x_1305__boxed_200_ = lean_unbox_usize(v_x_196_);
lean_dec(v_x_196_);
v_x_1306__boxed_201_ = lean_unbox_usize(v_x_197_);
lean_dec(v_x_197_);
v_x_1307__boxed_202_ = lean_unbox_uint64(v_x_198_);
lean_dec_ref(v_x_198_);
v_res_203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_x_195_, v_x_1305__boxed_200_, v_x_1306__boxed_201_, v_x_1307__boxed_202_, v_x_199_);
return v_res_203_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0___redArg(mut v_x_204_: *mut lean_object, mut v_x_205_: u64, mut v_x_206_: *mut lean_object) -> *mut lean_object{
let mut v___x_207_: usize = 0; let mut v___x_208_: usize = 0; let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); 
v___x_207_ = lean_uint64_to_usize(v_x_205_);
v___x_208_ = 1usize;
v___x_209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_x_204_, v___x_207_, v___x_208_, v_x_205_, v_x_206_);
return v___x_209_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0___redArg___boxed(mut v_x_210_: *mut lean_object, mut v_x_211_: *mut lean_object, mut v_x_212_: *mut lean_object) -> *mut lean_object{
let mut v_x_1473__boxed_213_: u64 = 0; let mut v_res_214_: *mut lean_object = core::ptr::null_mut(); 
v_x_1473__boxed_213_ = lean_unbox_uint64(v_x_211_);
lean_dec_ref(v_x_211_);
v_res_214_ = l_Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0___redArg(v_x_210_, v_x_1473__boxed_213_, v_x_212_);
return v_res_214_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mkMapWithCap_spec__2___redArg(mut v_a_215_: *mut lean_object, mut v_b_216_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_217_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_221_: u8 = 0; let mut v___x_222_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: u8 = 0; let mut v___x_224_: u64 = 0; let mut v___x_225_: u64 = 0; let mut v___x_226_: u64 = 0; let mut v___x_227_: u64 = 0; let mut v___x_228_: u64 = 0; let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_232_: *mut lean_object = core::ptr::null_mut(); let mut v___x_233_: u64 = 0; let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_236_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_237_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_217_ = lean_ctor_get(v_a_215_, 0);
v_inner_218_ = lean_ctor_get(v_a_215_, 1);
v_isSharedCheck_237_ = (!lean_is_exclusive(v_a_215_)) as u8;
if v_isSharedCheck_237_ == 0 {
v___x_220_ = v_a_215_;
v_isShared_221_ = v_isSharedCheck_237_;
state = 1; continue;
} else {
lean_inc(v_inner_218_);
lean_inc(v_countdown_217_);
lean_dec(v_a_215_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_237_;
state = 1; continue;
}
}
1 => {
v___x_222_ = lean_unsigned_to_nat(1);
v___x_223_ = lean_nat_dec_eq(v_countdown_217_, v___x_222_);
if v___x_223_ == 0 {
let mut v___x_224_: u64 = 0; let mut v___x_225_: u64 = 0; let mut v___x_226_: u64 = 0; let mut v___x_227_: u64 = 0; let mut v___x_228_: u64 = 0; let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_232_: *mut lean_object = core::ptr::null_mut(); 
v___x_224_ = 1u64;
v___x_225_ = lean_unbox_uint64(v_inner_218_);
v___x_226_ = lean_uint64_add(v___x_225_, v___x_224_);
v___x_227_ = 3787392781u64;
v___x_228_ = lean_uint64_mul(v___x_226_, v___x_227_);
v___x_229_ = lean_nat_sub(v_countdown_217_, v___x_222_);
lean_dec(v_countdown_217_);
v___x_230_ = lean_box_uint64(v___x_228_);
if v_isShared_221_ == 0 {
lean_ctor_set(v___x_220_, 1, v___x_230_);
lean_ctor_set(v___x_220_, 0, v___x_229_);
v___x_232_ = v___x_220_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_236_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_236_;
state = 2; continue;
}
} else {
lean_del_object(v___x_220_);
lean_dec(v_inner_218_);
lean_dec(v_countdown_217_);
return v_b_216_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mkMapWithCap(mut v_seed_238_: u64, mut v_size_239_: *mut lean_object) -> *mut lean_object{
let mut v_map_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_241_: *mut lean_object = core::ptr::null_mut(); let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); 
v_map_240_ = l_Lean_PersistentHashMap_empty___at___00mkMapWithCap_spec__1(lean_box(0));
v___x_241_ = lean_unsigned_to_nat(1);
v___x_242_ = lean_nat_add(v_size_239_, v___x_241_);
v___x_243_ = lean_box_uint64(v_seed_238_);
v___x_244_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_WellFounded_opaqueFix_u2083___at___00mkMapWithCap_spec__2___redArg(v___x_244_, v_map_240_);
return v___x_245_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkMapWithCap___boxed(mut v_seed_246_: *mut lean_object, mut v_size_247_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_248_: u64 = 0; let mut v_res_249_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_248_ = lean_unbox_uint64(v_seed_246_);
lean_dec_ref(v_seed_246_);
v_res_249_ = l_mkMapWithCap(v_seed_boxed_248_, v_size_247_);
lean_dec(v_size_247_);
return v_res_249_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0(mut v_00_u03b2_250_: *mut lean_object, mut v_x_251_: *mut lean_object, mut v_x_252_: u64, mut v_x_253_: *mut lean_object) -> *mut lean_object{
let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); 
v___x_254_ = l_Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0___redArg(v_x_251_, v_x_252_, v_x_253_);
return v___x_254_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0___boxed(mut v_00_u03b2_255_: *mut lean_object, mut v_x_256_: *mut lean_object, mut v_x_257_: *mut lean_object, mut v_x_258_: *mut lean_object) -> *mut lean_object{
let mut v_x_1536__boxed_259_: u64 = 0; let mut v_res_260_: *mut lean_object = core::ptr::null_mut(); 
v_x_1536__boxed_259_ = lean_unbox_uint64(v_x_257_);
lean_dec_ref(v_x_257_);
v_res_260_ = l_Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0(v_00_u03b2_255_, v_x_256_, v_x_1536__boxed_259_, v_x_258_);
return v_res_260_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00mkMapWithCap_spec__2(mut v_inst_261_: *mut lean_object, mut v_R_262_: *mut lean_object, mut v_a_263_: *mut lean_object, mut v_b_264_: *mut lean_object, mut v_c_265_: *mut lean_object) -> *mut lean_object{
let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); 
v___x_266_ = l_WellFounded_opaqueFix_u2083___at___00mkMapWithCap_spec__2___redArg(v_a_263_, v_b_264_);
return v___x_266_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0(mut v_00_u03b2_267_: *mut lean_object, mut v_x_268_: *mut lean_object, mut v_x_269_: usize, mut v_x_270_: usize, mut v_x_271_: u64, mut v_x_272_: *mut lean_object) -> *mut lean_object{
let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); 
v___x_273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0___redArg(v_x_268_, v_x_269_, v_x_270_, v_x_271_, v_x_272_);
return v___x_273_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0___boxed(mut v_00_u03b2_274_: *mut lean_object, mut v_x_275_: *mut lean_object, mut v_x_276_: *mut lean_object, mut v_x_277_: *mut lean_object, mut v_x_278_: *mut lean_object, mut v_x_279_: *mut lean_object) -> *mut lean_object{
let mut v_x_1551__boxed_280_: usize = 0; let mut v_x_1552__boxed_281_: usize = 0; let mut v_x_1553__boxed_282_: u64 = 0; let mut v_res_283_: *mut lean_object = core::ptr::null_mut(); 
v_x_1551__boxed_280_ = lean_unbox_usize(v_x_276_);
lean_dec(v_x_276_);
v_x_1552__boxed_281_ = lean_unbox_usize(v_x_277_);
lean_dec(v_x_277_);
v_x_1553__boxed_282_ = lean_unbox_uint64(v_x_278_);
lean_dec_ref(v_x_278_);
v_res_283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0(v_00_u03b2_274_, v_x_275_, v_x_1551__boxed_280_, v_x_1552__boxed_281_, v_x_1553__boxed_282_, v_x_279_);
return v_res_283_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2(mut v_00_u03b2_284_: *mut lean_object, mut v_n_285_: *mut lean_object, mut v_k_286_: u64, mut v_v_287_: *mut lean_object) -> *mut lean_object{
let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); 
v___x_288_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2___redArg(v_n_285_, v_k_286_, v_v_287_);
return v___x_288_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2___boxed(mut v_00_u03b2_289_: *mut lean_object, mut v_n_290_: *mut lean_object, mut v_k_291_: *mut lean_object, mut v_v_292_: *mut lean_object) -> *mut lean_object{
let mut v_k_boxed_293_: u64 = 0; let mut v_res_294_: *mut lean_object = core::ptr::null_mut(); 
v_k_boxed_293_ = lean_unbox_uint64(v_k_291_);
lean_dec_ref(v_k_291_);
v_res_294_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2(v_00_u03b2_289_, v_n_290_, v_k_boxed_293_, v_v_292_);
return v_res_294_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__3(mut v_00_u03b2_295_: *mut lean_object, mut v_depth_296_: usize, mut v_keys_297_: *mut lean_object, mut v_vals_298_: *mut lean_object, mut v_heq_299_: *mut lean_object, mut v_i_300_: *mut lean_object, mut v_entries_301_: *mut lean_object) -> *mut lean_object{
let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); 
v___x_302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__3___redArg(v_depth_296_, v_keys_297_, v_vals_298_, v_i_300_, v_entries_301_);
return v___x_302_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__3___boxed(mut v_00_u03b2_303_: *mut lean_object, mut v_depth_304_: *mut lean_object, mut v_keys_305_: *mut lean_object, mut v_vals_306_: *mut lean_object, mut v_heq_307_: *mut lean_object, mut v_i_308_: *mut lean_object, mut v_entries_309_: *mut lean_object) -> *mut lean_object{
let mut v_depth_boxed_310_: usize = 0; let mut v_res_311_: *mut lean_object = core::ptr::null_mut(); 
v_depth_boxed_310_ = lean_unbox_usize(v_depth_304_);
lean_dec(v_depth_304_);
v_res_311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__3(v_00_u03b2_303_, v_depth_boxed_310_, v_keys_305_, v_vals_306_, v_heq_307_, v_i_308_, v_entries_309_);
lean_dec_ref(v_vals_306_);
lean_dec_ref(v_keys_305_);
return v_res_311_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2_spec__4(mut v_00_u03b2_312_: *mut lean_object, mut v_x_313_: *mut lean_object, mut v_x_314_: *mut lean_object, mut v_x_315_: u64, mut v_x_316_: *mut lean_object) -> *mut lean_object{
let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); 
v___x_317_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2_spec__4___redArg(v_x_313_, v_x_314_, v_x_315_, v_x_316_);
return v___x_317_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2_spec__4___boxed(mut v_00_u03b2_318_: *mut lean_object, mut v_x_319_: *mut lean_object, mut v_x_320_: *mut lean_object, mut v_x_321_: *mut lean_object, mut v_x_322_: *mut lean_object) -> *mut lean_object{
let mut v_x_1573__boxed_323_: u64 = 0; let mut v_res_324_: *mut lean_object = core::ptr::null_mut(); 
v_x_1573__boxed_323_ = lean_unbox_uint64(v_x_321_);
lean_dec_ref(v_x_321_);
v_res_324_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_318_, v_x_319_, v_x_320_, v_x_1573__boxed_323_, v_x_322_);
return v_res_324_;
}
#[no_mangle] pub unsafe extern "C" fn l_timeNanos(mut v_reps_325_: *mut lean_object, mut v_x_326_: *mut lean_object) -> *mut lean_object{
let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_332_: u8 = 0; let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_335_: f64 = 0.0; let mut v___x_336_: f64 = 0.0; let mut v___x_337_: f64 = 0.0; let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_341_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_342_: u8 = 0; let mut v_unused_343_: *mut lean_object = core::ptr::null_mut(); let mut v_a_344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_347_: u8 = 0; let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_350_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_351_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_328_ = lean_io_mono_nanos_now();
v___x_329_ = lean_apply_1(v_x_326_, lean_box(0));
if lean_obj_tag(v___x_329_) == 0 {
let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_332_: u8 = 0; let mut v_isSharedCheck_342_: u8 = 0; 
v_isSharedCheck_342_ = (!lean_is_exclusive(v___x_329_)) as u8;
if v_isSharedCheck_342_ == 0 {
let mut v_unused_343_: *mut lean_object = core::ptr::null_mut(); 
v_unused_343_ = lean_ctor_get(v___x_329_, 0);
lean_dec(v_unused_343_);
v___x_331_ = v___x_329_;
v_isShared_332_ = v_isSharedCheck_342_;
state = 1; continue;
} else {
lean_dec(v___x_329_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_342_;
state = 1; continue;
}
} else {
let mut v_a_344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_347_: u8 = 0; let mut v_isSharedCheck_351_: u8 = 0; 
lean_dec(v___x_328_);
lean_dec(v_reps_325_);
v_a_344_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_351_ = (!lean_is_exclusive(v___x_329_)) as u8;
if v_isSharedCheck_351_ == 0 {
v___x_346_ = v___x_329_;
v_isShared_347_ = v_isSharedCheck_351_;
state = 3; continue;
} else {
lean_inc(v_a_344_);
lean_dec(v___x_329_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
state = 3; continue;
}
}
}
1 => {
v___x_333_ = lean_io_mono_nanos_now();
v___x_334_ = lean_nat_sub(v___x_333_, v___x_328_);
lean_dec(v___x_328_);
lean_dec(v___x_333_);
v___x_335_ = lean_float_of_nat(v___x_334_);
v___x_336_ = lean_float_of_nat(v_reps_325_);
v___x_337_ = lean_float_div(v___x_335_, v___x_336_);
v___x_338_ = lean_box_float(v___x_337_);
if v_isShared_332_ == 0 {
lean_ctor_set(v___x_331_, 0, v___x_338_);
v___x_340_ = v___x_331_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_341_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
state = 2; continue;
}
}
3 => {
if v_isShared_347_ == 0 {
v___x_349_ = v___x_346_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_350_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_timeNanos___boxed(mut v_reps_352_: *mut lean_object, mut v_x_353_: *mut lean_object, mut v_a_354_: *mut lean_object) -> *mut lean_object{
let mut v_res_355_: *mut lean_object = core::ptr::null_mut(); 
v_res_355_ = l_timeNanos(v_reps_352_, v_x_353_);
return v_res_355_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_REP() -> *mut lean_object{
let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); 
v___x_356_ = lean_unsigned_to_nat(100);
return v___x_356_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0_spec__1___redArg(mut v_keys_357_: *mut lean_object, mut v_i_358_: *mut lean_object, mut v_k_359_: u64) -> u8{
let mut v___x_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: u8 = 0; let mut v_k_x27_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: u64 = 0; let mut v___x_364_: u8 = 0; let mut v___x_365_: *mut lean_object = core::ptr::null_mut(); let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_360_ = lean_array_get_size(v_keys_357_);
v___x_361_ = lean_nat_dec_lt(v_i_358_, v___x_360_);
if v___x_361_ == 0 {
lean_dec(v_i_358_);
return v___x_361_;
} else {
let mut v_k_x27_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: u64 = 0; let mut v___x_364_: u8 = 0; 
v_k_x27_362_ = lean_array_fget_borrowed(v_keys_357_, v_i_358_);
v___x_363_ = lean_unbox_uint64(v_k_x27_362_);
v___x_364_ = lean_uint64_dec_eq(v_k_359_, v___x_363_);
if v___x_364_ == 0 {
let mut v___x_365_: *mut lean_object = core::ptr::null_mut(); let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); 
v___x_365_ = lean_unsigned_to_nat(1);
v___x_366_ = lean_nat_add(v_i_358_, v___x_365_);
lean_dec(v_i_358_);
v_i_358_ = v___x_366_;
state = 0; continue;
} else {
lean_dec(v_i_358_);
return v___x_364_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0_spec__1___redArg___boxed(mut v_keys_368_: *mut lean_object, mut v_i_369_: *mut lean_object, mut v_k_370_: *mut lean_object) -> *mut lean_object{
let mut v_k_boxed_371_: u64 = 0; let mut v_res_372_: u8 = 0; let mut v_r_373_: *mut lean_object = core::ptr::null_mut(); 
v_k_boxed_371_ = lean_unbox_uint64(v_k_370_);
lean_dec_ref(v_k_370_);
v_res_372_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0_spec__1___redArg(v_keys_368_, v_i_369_, v_k_boxed_371_);
lean_dec_ref(v_keys_368_);
v_r_373_ = lean_box((v_res_372_) as usize);
return v_r_373_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0___redArg(mut v_x_374_: *mut lean_object, mut v_x_375_: usize, mut v_x_376_: u64) -> u8{
let mut v_es_377_: *mut lean_object = core::ptr::null_mut(); let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_379_: usize = 0; let mut v___x_380_: usize = 0; let mut v___x_381_: usize = 0; let mut v___x_382_: usize = 0; let mut v___x_383_: usize = 0; let mut v_j_384_: *mut lean_object = core::ptr::null_mut(); let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); let mut v_key_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: u64 = 0; let mut v___x_388_: u8 = 0; let mut v_node_389_: *mut lean_object = core::ptr::null_mut(); let mut v___x_390_: usize = 0; let mut v___x_392_: u8 = 0; let mut v_ks_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_395_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_374_) == 0 {
let mut v_es_377_: *mut lean_object = core::ptr::null_mut(); let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_379_: usize = 0; let mut v___x_380_: usize = 0; let mut v___x_381_: usize = 0; let mut v___x_382_: usize = 0; let mut v___x_383_: usize = 0; let mut v_j_384_: *mut lean_object = core::ptr::null_mut(); let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); 
v_es_377_ = lean_ctor_get(v_x_374_, 0);
v___x_378_ = lean_box(2);
v___x_379_ = 5usize;
v___x_380_ = 1usize;
v___x_381_ = lean_usize_shift_left(v___x_380_, v___x_379_);
v___x_382_ = lean_usize_sub(v___x_381_, v___x_380_);
v___x_383_ = lean_usize_land(v_x_375_, v___x_382_);
v_j_384_ = lean_usize_to_nat(v___x_383_);
v___x_385_ = lean_array_get_borrowed(v___x_378_, v_es_377_, v_j_384_);
lean_dec(v_j_384_);
match lean_obj_tag(v___x_385_)
{
0 => {
let mut v_key_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: u64 = 0; let mut v___x_388_: u8 = 0; 
v_key_386_ = lean_ctor_get(v___x_385_, 0);
v___x_387_ = lean_unbox_uint64(v_key_386_);
v___x_388_ = lean_uint64_dec_eq(v_x_376_, v___x_387_);
return v___x_388_;
}
1 => {
let mut v_node_389_: *mut lean_object = core::ptr::null_mut(); let mut v___x_390_: usize = 0; 
v_node_389_ = lean_ctor_get(v___x_385_, 0);
v___x_390_ = lean_usize_shift_right(v_x_375_, v___x_379_);
v_x_374_ = v_node_389_;
v_x_375_ = v___x_390_;
state = 0; continue;
}
_ => {
let mut v___x_392_: u8 = 0; 
v___x_392_ = 0;
return v___x_392_;
}
}
} else {
let mut v_ks_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_395_: u8 = 0; 
v_ks_393_ = lean_ctor_get(v_x_374_, 0);
v___x_394_ = lean_unsigned_to_nat(0);
v___x_395_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0_spec__1___redArg(v_ks_393_, v___x_394_, v_x_376_);
return v___x_395_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0___redArg___boxed(mut v_x_396_: *mut lean_object, mut v_x_397_: *mut lean_object, mut v_x_398_: *mut lean_object) -> *mut lean_object{
let mut v_x_2300__boxed_399_: usize = 0; let mut v_x_2301__boxed_400_: u64 = 0; let mut v_res_401_: u8 = 0; let mut v_r_402_: *mut lean_object = core::ptr::null_mut(); 
v_x_2300__boxed_399_ = lean_unbox_usize(v_x_397_);
lean_dec(v_x_397_);
v_x_2301__boxed_400_ = lean_unbox_uint64(v_x_398_);
lean_dec_ref(v_x_398_);
v_res_401_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0___redArg(v_x_396_, v_x_2300__boxed_399_, v_x_2301__boxed_400_);
lean_dec_ref(v_x_396_);
v_r_402_ = lean_box((v_res_401_) as usize);
return v_r_402_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0___redArg(mut v_x_403_: *mut lean_object, mut v_x_404_: u64) -> u8{
let mut v___x_405_: usize = 0; let mut v___x_406_: u8 = 0; 
v___x_405_ = lean_uint64_to_usize(v_x_404_);
v___x_406_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0___redArg(v_x_403_, v___x_405_, v_x_404_);
return v___x_406_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0___redArg___boxed(mut v_x_407_: *mut lean_object, mut v_x_408_: *mut lean_object) -> *mut lean_object{
let mut v_x_2347__boxed_409_: u64 = 0; let mut v_res_410_: u8 = 0; let mut v_r_411_: *mut lean_object = core::ptr::null_mut(); 
v_x_2347__boxed_409_ = lean_unbox_uint64(v_x_408_);
lean_dec_ref(v_x_408_);
v_res_410_ = l_Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0___redArg(v_x_407_, v_x_2347__boxed_409_);
lean_dec_ref(v_x_407_);
v_r_411_ = lean_box((v_res_410_) as usize);
return v_r_411_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg(mut v_map_412_: *mut lean_object, mut v_a_413_: *mut lean_object, mut v_b_414_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_416_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_417_: *mut lean_object = core::ptr::null_mut(); let mut v___x_419_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_420_: u8 = 0; let mut v___x_421_: *mut lean_object = core::ptr::null_mut(); let mut v___x_422_: u8 = 0; let mut v___x_423_: u64 = 0; let mut v___x_424_: u64 = 0; let mut v___x_425_: u64 = 0; let mut v___x_426_: u64 = 0; let mut v___x_427_: u8 = 0; let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v___x_430_: *mut lean_object = core::ptr::null_mut(); let mut v___x_431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_432_: u64 = 0; let mut v___x_433_: u64 = 0; let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_437_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_439_: *mut lean_object = core::ptr::null_mut(); let mut v___x_440_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_441_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_416_ = lean_ctor_get(v_a_413_, 0);
v_inner_417_ = lean_ctor_get(v_a_413_, 1);
v_isSharedCheck_441_ = (!lean_is_exclusive(v_a_413_)) as u8;
if v_isSharedCheck_441_ == 0 {
v___x_419_ = v_a_413_;
v_isShared_420_ = v_isSharedCheck_441_;
state = 1; continue;
} else {
lean_inc(v_inner_417_);
lean_inc(v_countdown_416_);
lean_dec(v_a_413_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_441_;
state = 1; continue;
}
}
1 => {
v___x_421_ = lean_unsigned_to_nat(1);
v___x_422_ = lean_nat_dec_eq(v_countdown_416_, v___x_421_);
if v___x_422_ == 0 {
let mut v___x_423_: u64 = 0; let mut v___x_424_: u64 = 0; let mut v___x_425_: u64 = 0; let mut v___x_426_: u64 = 0; let mut v___x_427_: u8 = 0; 
v___x_423_ = 1u64;
v___x_424_ = lean_unbox_uint64(v_inner_417_);
v___x_425_ = lean_uint64_add(v___x_424_, v___x_423_);
v___x_426_ = lean_unbox_uint64(v_inner_417_);
lean_dec(v_inner_417_);
v___x_427_ = l_Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0___redArg(v_map_412_, v___x_426_);
if v___x_427_ == 0 {
let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v___x_430_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_419_);
lean_dec(v_countdown_416_);
v___x_428_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_429_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_429_, 0, v___x_428_);
v___x_430_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
} else {
let mut v___x_431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_432_: u64 = 0; let mut v___x_433_: u64 = 0; let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_437_: *mut lean_object = core::ptr::null_mut(); 
v___x_431_ = lean_box(0);
v___x_432_ = 3787392781u64;
v___x_433_ = lean_uint64_mul(v___x_425_, v___x_432_);
v___x_434_ = lean_nat_sub(v_countdown_416_, v___x_421_);
lean_dec(v_countdown_416_);
v___x_435_ = lean_box_uint64(v___x_433_);
if v_isShared_420_ == 0 {
lean_ctor_set(v___x_419_, 1, v___x_435_);
lean_ctor_set(v___x_419_, 0, v___x_434_);
v___x_437_ = v___x_419_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_439_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_435_);
v___x_437_ = v_reuseFailAlloc_439_;
state = 2; continue;
}
}
} else {
let mut v___x_440_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_419_);
lean_dec(v_inner_417_);
lean_dec(v_countdown_416_);
v___x_440_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_440_, 0, v_b_414_);
return v___x_440_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg___boxed(mut v_map_442_: *mut lean_object, mut v_a_443_: *mut lean_object, mut v_b_444_: *mut lean_object, mut v___y_445_: *mut lean_object) -> *mut lean_object{
let mut v_res_446_: *mut lean_object = core::ptr::null_mut(); 
v_res_446_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg(v_map_442_, v_a_443_, v_b_444_);
lean_dec_ref(v_map_442_);
return v_res_446_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg(mut v_seed_447_: u64, mut v_size_448_: *mut lean_object, mut v_map_449_: *mut lean_object, mut v_a_450_: *mut lean_object) -> *mut lean_object{
let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_453_: u8 = 0; let mut v___x_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); let mut v___x_458_: *mut lean_object = core::ptr::null_mut(); let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); let mut v___x_460_: *mut lean_object = core::ptr::null_mut(); let mut v_a_462_: *mut lean_object = core::ptr::null_mut(); let mut v___x_464_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_465_: u8 = 0; let mut v___x_467_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_468_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_469_: u8 = 0; let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_452_ = lean_unsigned_to_nat(0);
v___x_453_ = lean_nat_dec_eq(v_a_450_, v___x_452_);
if v___x_453_ == 0 {
let mut v___x_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); let mut v___x_458_: *mut lean_object = core::ptr::null_mut(); let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); 
v___x_454_ = lean_unsigned_to_nat(1);
v___x_455_ = lean_nat_add(v_size_448_, v___x_454_);
v___x_456_ = lean_box_uint64(v_seed_447_);
v___x_457_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_box(0);
v___x_459_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg(v_map_449_, v___x_457_, v___x_458_);
if lean_obj_tag(v___x_459_) == 0 {
let mut v___x_460_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_459_, 1);
v___x_460_ = lean_nat_sub(v_a_450_, v_size_448_);
lean_dec(v_a_450_);
v_a_450_ = v___x_460_;
state = 0; continue;
} else {
let mut v_a_462_: *mut lean_object = core::ptr::null_mut(); let mut v___x_464_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_465_: u8 = 0; let mut v_isSharedCheck_469_: u8 = 0; 
lean_dec(v_a_450_);
v_a_462_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_469_ = (!lean_is_exclusive(v___x_459_)) as u8;
if v_isSharedCheck_469_ == 0 {
v___x_464_ = v___x_459_;
v_isShared_465_ = v_isSharedCheck_469_;
state = 1; continue;
} else {
lean_inc(v_a_462_);
lean_dec(v___x_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
state = 1; continue;
}
}
} else {
let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); 
v___x_470_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_470_, 0, v_a_450_);
return v___x_470_;
}
}
1 => {
if v_isShared_465_ == 0 {
v___x_467_ = v___x_464_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_468_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg___boxed(mut v_seed_471_: *mut lean_object, mut v_size_472_: *mut lean_object, mut v_map_473_: *mut lean_object, mut v_a_474_: *mut lean_object, mut v___y_475_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_476_: u64 = 0; let mut v_res_477_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_476_ = lean_unbox_uint64(v_seed_471_);
lean_dec_ref(v_seed_471_);
v_res_477_ = l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg(v_seed_boxed_476_, v_size_472_, v_map_473_, v_a_474_);
lean_dec_ref(v_map_473_);
lean_dec(v_size_472_);
return v_res_477_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsHit___lam__0(mut v_seed_478_: u64, mut v_size_479_: *mut lean_object, mut v_map_480_: *mut lean_object, mut v_todo_481_: *mut lean_object) -> *mut lean_object{
let mut v___x_483_: *mut lean_object = core::ptr::null_mut(); let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_486_: u8 = 0; let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_489_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_490_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_491_: u8 = 0; let mut v_unused_492_: *mut lean_object = core::ptr::null_mut(); let mut v_a_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_496_: u8 = 0; let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_499_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_500_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_483_ = l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg(v_seed_478_, v_size_479_, v_map_480_, v_todo_481_);
if lean_obj_tag(v___x_483_) == 0 {
let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_486_: u8 = 0; let mut v_isSharedCheck_491_: u8 = 0; 
v_isSharedCheck_491_ = (!lean_is_exclusive(v___x_483_)) as u8;
if v_isSharedCheck_491_ == 0 {
let mut v_unused_492_: *mut lean_object = core::ptr::null_mut(); 
v_unused_492_ = lean_ctor_get(v___x_483_, 0);
lean_dec(v_unused_492_);
v___x_485_ = v___x_483_;
v_isShared_486_ = v_isSharedCheck_491_;
state = 1; continue;
} else {
lean_dec(v___x_483_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_491_;
state = 1; continue;
}
} else {
let mut v_a_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_496_: u8 = 0; let mut v_isSharedCheck_500_: u8 = 0; 
v_a_493_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_500_ = (!lean_is_exclusive(v___x_483_)) as u8;
if v_isSharedCheck_500_ == 0 {
v___x_495_ = v___x_483_;
v_isShared_496_ = v_isSharedCheck_500_;
state = 3; continue;
} else {
lean_inc(v_a_493_);
lean_dec(v___x_483_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
state = 3; continue;
}
}
}
1 => {
v___x_487_ = lean_box(0);
if v_isShared_486_ == 0 {
lean_ctor_set(v___x_485_, 0, v___x_487_);
v___x_489_ = v___x_485_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_490_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
state = 2; continue;
}
}
3 => {
if v_isShared_496_ == 0 {
v___x_498_ = v___x_495_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_499_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsHit___lam__0___boxed(mut v_seed_501_: *mut lean_object, mut v_size_502_: *mut lean_object, mut v_map_503_: *mut lean_object, mut v_todo_504_: *mut lean_object, mut v___y_505_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_506_: u64 = 0; let mut v_res_507_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_506_ = lean_unbox_uint64(v_seed_501_);
lean_dec_ref(v_seed_501_);
v_res_507_ = l_benchContainsHit___lam__0(v_seed_boxed_506_, v_size_502_, v_map_503_, v_todo_504_);
lean_dec_ref(v_map_503_);
lean_dec(v_size_502_);
return v_res_507_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsHit(mut v_seed_508_: u64, mut v_size_509_: *mut lean_object) -> *mut lean_object{
let mut v_map_511_: *mut lean_object = core::ptr::null_mut(); let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_513_: *mut lean_object = core::ptr::null_mut(); let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); let mut v___f_515_: *mut lean_object = core::ptr::null_mut(); let mut v___x_516_: *mut lean_object = core::ptr::null_mut(); 
v_map_511_ = l_mkMapWithCap(v_seed_508_, v_size_509_);
v___x_512_ = lean_unsigned_to_nat(100);
v_todo_513_ = lean_nat_mul(v_size_509_, v___x_512_);
v___x_514_ = lean_box_uint64(v_seed_508_);
lean_inc(v_todo_513_);
v___f_515_ = lean_alloc_closure(l_benchContainsHit___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
lean_closure_set(v___f_515_, 0, v___x_514_);
lean_closure_set(v___f_515_, 1, v_size_509_);
lean_closure_set(v___f_515_, 2, v_map_511_);
lean_closure_set(v___f_515_, 3, v_todo_513_);
v___x_516_ = l_timeNanos(v_todo_513_, v___f_515_);
return v___x_516_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsHit___boxed(mut v_seed_517_: *mut lean_object, mut v_size_518_: *mut lean_object, mut v_a_519_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_520_: u64 = 0; let mut v_res_521_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_520_ = lean_unbox_uint64(v_seed_517_);
lean_dec_ref(v_seed_517_);
v_res_521_ = l_benchContainsHit(v_seed_boxed_520_, v_size_518_);
return v_res_521_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0(mut v_00_u03b2_522_: *mut lean_object, mut v_x_523_: *mut lean_object, mut v_x_524_: u64) -> u8{
let mut v___x_525_: u8 = 0; 
v___x_525_ = l_Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0___redArg(v_x_523_, v_x_524_);
return v___x_525_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0___boxed(mut v_00_u03b2_526_: *mut lean_object, mut v_x_527_: *mut lean_object, mut v_x_528_: *mut lean_object) -> *mut lean_object{
let mut v_x_2501__boxed_529_: u64 = 0; let mut v_res_530_: u8 = 0; let mut v_r_531_: *mut lean_object = core::ptr::null_mut(); 
v_x_2501__boxed_529_ = lean_unbox_uint64(v_x_528_);
lean_dec_ref(v_x_528_);
v_res_530_ = l_Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0(v_00_u03b2_526_, v_x_527_, v_x_2501__boxed_529_);
lean_dec_ref(v_x_527_);
v_r_531_ = lean_box((v_res_530_) as usize);
return v_r_531_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1(mut v_map_532_: *mut lean_object, mut v_inst_533_: *mut lean_object, mut v_R_534_: *mut lean_object, mut v_a_535_: *mut lean_object, mut v_b_536_: *mut lean_object, mut v_c_537_: *mut lean_object) -> *mut lean_object{
let mut v___x_539_: *mut lean_object = core::ptr::null_mut(); 
v___x_539_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___redArg(v_map_532_, v_a_535_, v_b_536_);
return v___x_539_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1___boxed(mut v_map_540_: *mut lean_object, mut v_inst_541_: *mut lean_object, mut v_R_542_: *mut lean_object, mut v_a_543_: *mut lean_object, mut v_b_544_: *mut lean_object, mut v_c_545_: *mut lean_object, mut v___y_546_: *mut lean_object) -> *mut lean_object{
let mut v_res_547_: *mut lean_object = core::ptr::null_mut(); 
v_res_547_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsHit_spec__1(v_map_540_, v_inst_541_, v_R_542_, v_a_543_, v_b_544_, v_c_545_);
lean_dec_ref(v_map_540_);
return v_res_547_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2(mut v_seed_548_: u64, mut v_size_549_: *mut lean_object, mut v_map_550_: *mut lean_object, mut v_inst_551_: *mut lean_object, mut v_a_552_: *mut lean_object) -> *mut lean_object{
let mut v___x_554_: *mut lean_object = core::ptr::null_mut(); 
v___x_554_ = l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___redArg(v_seed_548_, v_size_549_, v_map_550_, v_a_552_);
return v___x_554_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2___boxed(mut v_seed_555_: *mut lean_object, mut v_size_556_: *mut lean_object, mut v_map_557_: *mut lean_object, mut v_inst_558_: *mut lean_object, mut v_a_559_: *mut lean_object, mut v___y_560_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_561_: u64 = 0; let mut v_res_562_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_561_ = lean_unbox_uint64(v_seed_555_);
lean_dec_ref(v_seed_555_);
v_res_562_ = l___private_Init_While_0__whileM_erased___at___00benchContainsHit_spec__2(v_seed_boxed_561_, v_size_556_, v_map_557_, v_inst_558_, v_a_559_);
lean_dec_ref(v_map_557_);
lean_dec(v_size_556_);
return v_res_562_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0(mut v_00_u03b2_563_: *mut lean_object, mut v_x_564_: *mut lean_object, mut v_x_565_: usize, mut v_x_566_: u64) -> u8{
let mut v___x_567_: u8 = 0; 
v___x_567_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0___redArg(v_x_564_, v_x_565_, v_x_566_);
return v___x_567_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0___boxed(mut v_00_u03b2_568_: *mut lean_object, mut v_x_569_: *mut lean_object, mut v_x_570_: *mut lean_object, mut v_x_571_: *mut lean_object) -> *mut lean_object{
let mut v_x_2525__boxed_572_: usize = 0; let mut v_x_2526__boxed_573_: u64 = 0; let mut v_res_574_: u8 = 0; let mut v_r_575_: *mut lean_object = core::ptr::null_mut(); 
v_x_2525__boxed_572_ = lean_unbox_usize(v_x_570_);
lean_dec(v_x_570_);
v_x_2526__boxed_573_ = lean_unbox_uint64(v_x_571_);
lean_dec_ref(v_x_571_);
v_res_574_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0(v_00_u03b2_568_, v_x_569_, v_x_2525__boxed_572_, v_x_2526__boxed_573_);
lean_dec_ref(v_x_569_);
v_r_575_ = lean_box((v_res_574_) as usize);
return v_r_575_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0_spec__1(mut v_00_u03b2_576_: *mut lean_object, mut v_keys_577_: *mut lean_object, mut v_vals_578_: *mut lean_object, mut v_heq_579_: *mut lean_object, mut v_i_580_: *mut lean_object, mut v_k_581_: u64) -> u8{
let mut v___x_582_: u8 = 0; 
v___x_582_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0_spec__1___redArg(v_keys_577_, v_i_580_, v_k_581_);
return v___x_582_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0_spec__1___boxed(mut v_00_u03b2_583_: *mut lean_object, mut v_keys_584_: *mut lean_object, mut v_vals_585_: *mut lean_object, mut v_heq_586_: *mut lean_object, mut v_i_587_: *mut lean_object, mut v_k_588_: *mut lean_object) -> *mut lean_object{
let mut v_k_boxed_589_: u64 = 0; let mut v_res_590_: u8 = 0; let mut v_r_591_: *mut lean_object = core::ptr::null_mut(); 
v_k_boxed_589_ = lean_unbox_uint64(v_k_588_);
lean_dec_ref(v_k_588_);
v_res_590_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00benchContainsHit_spec__0_spec__0_spec__1(v_00_u03b2_583_, v_keys_584_, v_vals_585_, v_heq_586_, v_i_587_, v_k_boxed_589_);
lean_dec_ref(v_vals_585_);
lean_dec_ref(v_keys_584_);
v_r_591_ = lean_box((v_res_590_) as usize);
return v_r_591_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg(mut v_map_592_: *mut lean_object, mut v_a_593_: *mut lean_object, mut v_b_594_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_596_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_597_: *mut lean_object = core::ptr::null_mut(); let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_600_: u8 = 0; let mut v___x_601_: *mut lean_object = core::ptr::null_mut(); let mut v___x_602_: u8 = 0; let mut v_remaining_603_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_606_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_607_: u8 = 0; let mut v___x_608_: u64 = 0; let mut v___x_609_: u64 = 0; let mut v___x_610_: u64 = 0; let mut v___x_611_: u64 = 0; let mut v___x_612_: u64 = 0; let mut v_zero_613_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_614_: u8 = 0; let mut v___x_615_: u64 = 0; let mut v___x_616_: u8 = 0; let mut v___x_617_: *mut lean_object = core::ptr::null_mut(); let mut v___x_618_: *mut lean_object = core::ptr::null_mut(); let mut v___x_620_: *mut lean_object = core::ptr::null_mut(); let mut v___x_621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_623_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_625_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_626_: *mut lean_object = core::ptr::null_mut(); let mut v___x_627_: *mut lean_object = core::ptr::null_mut(); let mut v___x_628_: *mut lean_object = core::ptr::null_mut(); let mut v___x_629_: *mut lean_object = core::ptr::null_mut(); let mut v_n_630_: *mut lean_object = core::ptr::null_mut(); let mut v___x_631_: *mut lean_object = core::ptr::null_mut(); let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); let mut v___x_635_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_637_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_638_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_639_: u8 = 0; let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_641_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_596_ = lean_ctor_get(v_a_593_, 0);
v_inner_597_ = lean_ctor_get(v_a_593_, 1);
v_isSharedCheck_641_ = (!lean_is_exclusive(v_a_593_)) as u8;
if v_isSharedCheck_641_ == 0 {
v___x_599_ = v_a_593_;
v_isShared_600_ = v_isSharedCheck_641_;
state = 1; continue;
} else {
lean_inc(v_inner_597_);
lean_inc(v_countdown_596_);
lean_dec(v_a_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_641_;
state = 1; continue;
}
}
1 => {
v___x_601_ = lean_unsigned_to_nat(1);
v___x_602_ = lean_nat_dec_eq(v_countdown_596_, v___x_601_);
if v___x_602_ == 0 {
let mut v_remaining_603_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_606_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_607_: u8 = 0; let mut v_isSharedCheck_639_: u8 = 0; 
v_remaining_603_ = lean_ctor_get(v_inner_597_, 0);
v_inner_604_ = lean_ctor_get(v_inner_597_, 1);
v_isSharedCheck_639_ = (!lean_is_exclusive(v_inner_597_)) as u8;
if v_isSharedCheck_639_ == 0 {
v___x_606_ = v_inner_597_;
v_isShared_607_ = v_isSharedCheck_639_;
state = 2; continue;
} else {
lean_inc(v_inner_604_);
lean_inc(v_remaining_603_);
lean_dec(v_inner_597_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_639_;
state = 2; continue;
}
} else {
let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_599_);
lean_dec(v_inner_597_);
lean_dec(v_countdown_596_);
v___x_640_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_640_, 0, v_b_594_);
return v___x_640_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg___boxed(mut v_map_642_: *mut lean_object, mut v_a_643_: *mut lean_object, mut v_b_644_: *mut lean_object, mut v___y_645_: *mut lean_object) -> *mut lean_object{
let mut v_res_646_: *mut lean_object = core::ptr::null_mut(); 
v_res_646_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg(v_map_642_, v_a_643_, v_b_644_);
lean_dec_ref(v_map_642_);
return v_res_646_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg(mut v_iter_647_: *mut lean_object, mut v_size_648_: *mut lean_object, mut v_map_649_: *mut lean_object, mut v_a_650_: *mut lean_object) -> *mut lean_object{
let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: u8 = 0; let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_656_: *mut lean_object = core::ptr::null_mut(); let mut v___x_657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_659_: *mut lean_object = core::ptr::null_mut(); let mut v_a_661_: *mut lean_object = core::ptr::null_mut(); let mut v___x_663_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_664_: u8 = 0; let mut v___x_666_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_667_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_668_: u8 = 0; let mut v___x_669_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_652_ = lean_unsigned_to_nat(0);
v___x_653_ = lean_nat_dec_eq(v_a_650_, v___x_652_);
if v___x_653_ == 0 {
let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v___x_655_: *mut lean_object = core::ptr::null_mut(); let mut v___x_656_: *mut lean_object = core::ptr::null_mut(); let mut v___x_657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_658_: *mut lean_object = core::ptr::null_mut(); 
v___x_654_ = lean_unsigned_to_nat(1);
v___x_655_ = lean_nat_add(v_size_648_, v___x_654_);
lean_inc_ref(v_iter_647_);
v___x_656_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v_iter_647_);
v___x_657_ = lean_box(0);
v___x_658_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg(v_map_649_, v___x_656_, v___x_657_);
if lean_obj_tag(v___x_658_) == 0 {
let mut v___x_659_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_658_, 1);
v___x_659_ = lean_nat_sub(v_a_650_, v_size_648_);
lean_dec(v_a_650_);
v_a_650_ = v___x_659_;
state = 0; continue;
} else {
let mut v_a_661_: *mut lean_object = core::ptr::null_mut(); let mut v___x_663_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_664_: u8 = 0; let mut v_isSharedCheck_668_: u8 = 0; 
lean_dec(v_a_650_);
lean_dec_ref(v_iter_647_);
v_a_661_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_668_ = (!lean_is_exclusive(v___x_658_)) as u8;
if v_isSharedCheck_668_ == 0 {
v___x_663_ = v___x_658_;
v_isShared_664_ = v_isSharedCheck_668_;
state = 1; continue;
} else {
lean_inc(v_a_661_);
lean_dec(v___x_658_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
state = 1; continue;
}
}
} else {
let mut v___x_669_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_iter_647_);
v___x_669_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_669_, 0, v_a_650_);
return v___x_669_;
}
}
1 => {
if v_isShared_664_ == 0 {
v___x_666_ = v___x_663_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_667_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg___boxed(mut v_iter_670_: *mut lean_object, mut v_size_671_: *mut lean_object, mut v_map_672_: *mut lean_object, mut v_a_673_: *mut lean_object, mut v___y_674_: *mut lean_object) -> *mut lean_object{
let mut v_res_675_: *mut lean_object = core::ptr::null_mut(); 
v_res_675_ = l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg(v_iter_670_, v_size_671_, v_map_672_, v_a_673_);
lean_dec_ref(v_map_672_);
lean_dec(v_size_671_);
return v_res_675_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsMiss___lam__0(mut v_iter_676_: *mut lean_object, mut v_size_677_: *mut lean_object, mut v_map_678_: *mut lean_object, mut v_todo_679_: *mut lean_object) -> *mut lean_object{
let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_684_: u8 = 0; let mut v___x_685_: *mut lean_object = core::ptr::null_mut(); let mut v___x_687_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_688_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_689_: u8 = 0; let mut v_unused_690_: *mut lean_object = core::ptr::null_mut(); let mut v_a_691_: *mut lean_object = core::ptr::null_mut(); let mut v___x_693_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_694_: u8 = 0; let mut v___x_696_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_697_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_698_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_681_ = l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg(v_iter_676_, v_size_677_, v_map_678_, v_todo_679_);
if lean_obj_tag(v___x_681_) == 0 {
let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_684_: u8 = 0; let mut v_isSharedCheck_689_: u8 = 0; 
v_isSharedCheck_689_ = (!lean_is_exclusive(v___x_681_)) as u8;
if v_isSharedCheck_689_ == 0 {
let mut v_unused_690_: *mut lean_object = core::ptr::null_mut(); 
v_unused_690_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_690_);
v___x_683_ = v___x_681_;
v_isShared_684_ = v_isSharedCheck_689_;
state = 1; continue;
} else {
lean_dec(v___x_681_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_689_;
state = 1; continue;
}
} else {
let mut v_a_691_: *mut lean_object = core::ptr::null_mut(); let mut v___x_693_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_694_: u8 = 0; let mut v_isSharedCheck_698_: u8 = 0; 
v_a_691_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_698_ = (!lean_is_exclusive(v___x_681_)) as u8;
if v_isSharedCheck_698_ == 0 {
v___x_693_ = v___x_681_;
v_isShared_694_ = v_isSharedCheck_698_;
state = 3; continue;
} else {
lean_inc(v_a_691_);
lean_dec(v___x_681_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
state = 3; continue;
}
}
}
1 => {
v___x_685_ = lean_box(0);
if v_isShared_684_ == 0 {
lean_ctor_set(v___x_683_, 0, v___x_685_);
v___x_687_ = v___x_683_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_688_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
state = 2; continue;
}
}
3 => {
if v_isShared_694_ == 0 {
v___x_696_ = v___x_693_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_697_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsMiss___lam__0___boxed(mut v_iter_699_: *mut lean_object, mut v_size_700_: *mut lean_object, mut v_map_701_: *mut lean_object, mut v_todo_702_: *mut lean_object, mut v___y_703_: *mut lean_object) -> *mut lean_object{
let mut v_res_704_: *mut lean_object = core::ptr::null_mut(); 
v_res_704_ = l_benchContainsMiss___lam__0(v_iter_699_, v_size_700_, v_map_701_, v_todo_702_);
lean_dec_ref(v_map_701_);
lean_dec(v_size_700_);
return v_res_704_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsMiss(mut v_seed_705_: u64, mut v_size_706_: *mut lean_object) -> *mut lean_object{
let mut v_map_708_: *mut lean_object = core::ptr::null_mut(); let mut v___x_709_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_710_: *mut lean_object = core::ptr::null_mut(); let mut v___x_711_: *mut lean_object = core::ptr::null_mut(); let mut v_iter_712_: *mut lean_object = core::ptr::null_mut(); let mut v___f_713_: *mut lean_object = core::ptr::null_mut(); let mut v___x_714_: *mut lean_object = core::ptr::null_mut(); 
v_map_708_ = l_mkMapWithCap(v_seed_705_, v_size_706_);
v___x_709_ = lean_unsigned_to_nat(100);
v_todo_710_ = lean_nat_mul(v_size_706_, v___x_709_);
v___x_711_ = lean_box_uint64(v_seed_705_);
lean_inc(v_size_706_);
v_iter_712_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_iter_712_, 0, v_size_706_);
lean_ctor_set(v_iter_712_, 1, v___x_711_);
lean_inc(v_todo_710_);
v___f_713_ = lean_alloc_closure(l_benchContainsMiss___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
lean_closure_set(v___f_713_, 0, v_iter_712_);
lean_closure_set(v___f_713_, 1, v_size_706_);
lean_closure_set(v___f_713_, 2, v_map_708_);
lean_closure_set(v___f_713_, 3, v_todo_710_);
v___x_714_ = l_timeNanos(v_todo_710_, v___f_713_);
return v___x_714_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchContainsMiss___boxed(mut v_seed_715_: *mut lean_object, mut v_size_716_: *mut lean_object, mut v_a_717_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_718_: u64 = 0; let mut v_res_719_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_718_ = lean_unbox_uint64(v_seed_715_);
lean_dec_ref(v_seed_715_);
v_res_719_ = l_benchContainsMiss(v_seed_boxed_718_, v_size_716_);
return v_res_719_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0(mut v_map_720_: *mut lean_object, mut v_inst_721_: *mut lean_object, mut v_R_722_: *mut lean_object, mut v_a_723_: *mut lean_object, mut v_b_724_: *mut lean_object, mut v_c_725_: *mut lean_object) -> *mut lean_object{
let mut v___x_727_: *mut lean_object = core::ptr::null_mut(); 
v___x_727_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___redArg(v_map_720_, v_a_723_, v_b_724_);
return v___x_727_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0___boxed(mut v_map_728_: *mut lean_object, mut v_inst_729_: *mut lean_object, mut v_R_730_: *mut lean_object, mut v_a_731_: *mut lean_object, mut v_b_732_: *mut lean_object, mut v_c_733_: *mut lean_object, mut v___y_734_: *mut lean_object) -> *mut lean_object{
let mut v_res_735_: *mut lean_object = core::ptr::null_mut(); 
v_res_735_ = l_WellFounded_opaqueFix_u2083___at___00benchContainsMiss_spec__0(v_map_728_, v_inst_729_, v_R_730_, v_a_731_, v_b_732_, v_c_733_);
lean_dec_ref(v_map_728_);
return v_res_735_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1(mut v_iter_736_: *mut lean_object, mut v_size_737_: *mut lean_object, mut v_map_738_: *mut lean_object, mut v_inst_739_: *mut lean_object, mut v_a_740_: *mut lean_object) -> *mut lean_object{
let mut v___x_742_: *mut lean_object = core::ptr::null_mut(); 
v___x_742_ = l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___redArg(v_iter_736_, v_size_737_, v_map_738_, v_a_740_);
return v___x_742_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1___boxed(mut v_iter_743_: *mut lean_object, mut v_size_744_: *mut lean_object, mut v_map_745_: *mut lean_object, mut v_inst_746_: *mut lean_object, mut v_a_747_: *mut lean_object, mut v___y_748_: *mut lean_object) -> *mut lean_object{
let mut v_res_749_: *mut lean_object = core::ptr::null_mut(); 
v_res_749_ = l___private_Init_While_0__whileM_erased___at___00benchContainsMiss_spec__1(v_iter_743_, v_size_744_, v_map_745_, v_inst_746_, v_a_747_);
lean_dec_ref(v_map_745_);
lean_dec(v_size_744_);
return v_res_749_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__4___redArg(mut v_f_750_: *mut lean_object, mut v_keys_751_: *mut lean_object, mut v_vals_752_: *mut lean_object, mut v_i_753_: *mut lean_object, mut v_acc_754_: *mut lean_object) -> *mut lean_object{
let mut v___x_756_: *mut lean_object = core::ptr::null_mut(); let mut v___x_757_: u8 = 0; let mut v___x_758_: *mut lean_object = core::ptr::null_mut(); let mut v___x_759_: *mut lean_object = core::ptr::null_mut(); let mut v_k_760_: *mut lean_object = core::ptr::null_mut(); let mut v_v_761_: *mut lean_object = core::ptr::null_mut(); let mut v___x_762_: *mut lean_object = core::ptr::null_mut(); let mut v_a_763_: *mut lean_object = core::ptr::null_mut(); let mut v_a_764_: *mut lean_object = core::ptr::null_mut(); let mut v___x_765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_766_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_756_ = lean_array_get_size(v_keys_751_);
v___x_757_ = lean_nat_dec_lt(v_i_753_, v___x_756_);
if v___x_757_ == 0 {
let mut v___x_758_: *mut lean_object = core::ptr::null_mut(); let mut v___x_759_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_753_);
lean_dec_ref(v_f_750_);
v___x_758_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_758_, 0, v_acc_754_);
v___x_759_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
} else {
let mut v_k_760_: *mut lean_object = core::ptr::null_mut(); let mut v_v_761_: *mut lean_object = core::ptr::null_mut(); let mut v___x_762_: *mut lean_object = core::ptr::null_mut(); 
v_k_760_ = lean_array_fget_borrowed(v_keys_751_, v_i_753_);
v_v_761_ = lean_array_fget_borrowed(v_vals_752_, v_i_753_);
lean_inc_ref(v_f_750_);
lean_inc(v_v_761_);
lean_inc(v_k_760_);
v___x_762_ = lean_apply_4(v_f_750_, v_acc_754_, v_k_760_, v_v_761_, lean_box(0));
if lean_obj_tag(v___x_762_) == 0 {
let mut v_a_763_: *mut lean_object = core::ptr::null_mut(); 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
if lean_obj_tag(v_a_763_) == 0 {
lean_dec_ref_known(v_a_763_, 1);
lean_dec(v_i_753_);
lean_dec_ref(v_f_750_);
return v___x_762_;
} else {
let mut v_a_764_: *mut lean_object = core::ptr::null_mut(); let mut v___x_765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_766_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_762_, 1);
v_a_764_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v_a_763_, 1);
v___x_765_ = lean_unsigned_to_nat(1);
v___x_766_ = lean_nat_add(v_i_753_, v___x_765_);
lean_dec(v_i_753_);
v_i_753_ = v___x_766_;
v_acc_754_ = v_a_764_;
state = 0; continue;
}
} else {
lean_dec(v_i_753_);
lean_dec_ref(v_f_750_);
return v___x_762_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__4___redArg___boxed(mut v_f_768_: *mut lean_object, mut v_keys_769_: *mut lean_object, mut v_vals_770_: *mut lean_object, mut v_i_771_: *mut lean_object, mut v_acc_772_: *mut lean_object, mut v___y_773_: *mut lean_object) -> *mut lean_object{
let mut v_res_774_: *mut lean_object = core::ptr::null_mut(); 
v_res_774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__4___redArg(v_f_768_, v_keys_769_, v_vals_770_, v_i_771_, v_acc_772_);
lean_dec_ref(v_vals_770_);
lean_dec_ref(v_keys_769_);
return v_res_774_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___redArg(mut v_f_775_: *mut lean_object, mut v_x_776_: *mut lean_object, mut v_x_777_: *mut lean_object) -> *mut lean_object{
let mut v_es_779_: *mut lean_object = core::ptr::null_mut(); let mut v___x_781_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_782_: u8 = 0; let mut v___x_783_: *mut lean_object = core::ptr::null_mut(); let mut v___x_784_: *mut lean_object = core::ptr::null_mut(); let mut v___x_785_: u8 = 0; let mut v___x_787_: *mut lean_object = core::ptr::null_mut(); let mut v___x_788_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_789_: *mut lean_object = core::ptr::null_mut(); let mut v___x_790_: u8 = 0; let mut v___x_792_: *mut lean_object = core::ptr::null_mut(); let mut v___x_793_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_794_: *mut lean_object = core::ptr::null_mut(); let mut v___x_795_: usize = 0; let mut v___x_796_: usize = 0; let mut v___x_797_: *mut lean_object = core::ptr::null_mut(); let mut v___x_798_: usize = 0; let mut v___x_799_: usize = 0; let mut v___x_800_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_801_: u8 = 0; let mut v_ks_802_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_803_: *mut lean_object = core::ptr::null_mut(); let mut v___x_804_: *mut lean_object = core::ptr::null_mut(); let mut v___x_805_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_776_) == 0 {
let mut v_es_779_: *mut lean_object = core::ptr::null_mut(); let mut v___x_781_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_782_: u8 = 0; let mut v_isSharedCheck_801_: u8 = 0; 
v_es_779_ = lean_ctor_get(v_x_776_, 0);
v_isSharedCheck_801_ = (!lean_is_exclusive(v_x_776_)) as u8;
if v_isSharedCheck_801_ == 0 {
v___x_781_ = v_x_776_;
v_isShared_782_ = v_isSharedCheck_801_;
state = 1; continue;
} else {
lean_inc(v_es_779_);
lean_dec(v_x_776_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_801_;
state = 1; continue;
}
} else {
let mut v_ks_802_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_803_: *mut lean_object = core::ptr::null_mut(); let mut v___x_804_: *mut lean_object = core::ptr::null_mut(); let mut v___x_805_: *mut lean_object = core::ptr::null_mut(); 
v_ks_802_ = lean_ctor_get(v_x_776_, 0);
lean_inc_ref(v_ks_802_);
v_vs_803_ = lean_ctor_get(v_x_776_, 1);
lean_inc_ref(v_vs_803_);
lean_dec_ref_known(v_x_776_, 2);
v___x_804_ = lean_unsigned_to_nat(0);
v___x_805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__4___redArg(v_f_775_, v_ks_802_, v_vs_803_, v___x_804_, v_x_777_);
lean_dec_ref(v_vs_803_);
lean_dec_ref(v_ks_802_);
return v___x_805_;
}
}
1 => {
v___x_783_ = lean_unsigned_to_nat(0);
v___x_784_ = lean_array_get_size(v_es_779_);
v___x_785_ = lean_nat_dec_lt(v___x_783_, v___x_784_);
if v___x_785_ == 0 {
let mut v___x_787_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_es_779_);
lean_dec_ref(v_f_775_);
if v_isShared_782_ == 0 {
lean_ctor_set_tag(v___x_781_, 1);
lean_ctor_set(v___x_781_, 0, v_x_777_);
v___x_787_ = v___x_781_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_789_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_x_777_);
v___x_787_ = v_reuseFailAlloc_789_;
state = 2; continue;
}
} else {
let mut v___x_790_: u8 = 0; 
v___x_790_ = lean_nat_dec_le(v___x_784_, v___x_784_);
if v___x_790_ == 0 {
if v___x_785_ == 0 {
let mut v___x_792_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_es_779_);
lean_dec_ref(v_f_775_);
if v_isShared_782_ == 0 {
lean_ctor_set_tag(v___x_781_, 1);
lean_ctor_set(v___x_781_, 0, v_x_777_);
v___x_792_ = v___x_781_;
state = 3; continue;
} else {
let mut v_reuseFailAlloc_794_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_x_777_);
v___x_792_ = v_reuseFailAlloc_794_;
state = 3; continue;
}
} else {
let mut v___x_795_: usize = 0; let mut v___x_796_: usize = 0; let mut v___x_797_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_781_);
v___x_795_ = 0usize;
v___x_796_ = lean_usize_of_nat(v___x_784_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3___redArg(v_f_775_, v_es_779_, v___x_795_, v___x_796_, v_x_777_);
lean_dec_ref(v_es_779_);
return v___x_797_;
}
} else {
let mut v___x_798_: usize = 0; let mut v___x_799_: usize = 0; let mut v___x_800_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_781_);
v___x_798_ = 0usize;
v___x_799_ = lean_usize_of_nat(v___x_784_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3___redArg(v_f_775_, v_es_779_, v___x_798_, v___x_799_, v_x_777_);
lean_dec_ref(v_es_779_);
return v___x_800_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3___redArg(mut v_f_806_: *mut lean_object, mut v_as_807_: *mut lean_object, mut v_i_808_: usize, mut v_stop_809_: usize, mut v_b_810_: *mut lean_object) -> *mut lean_object{
let mut v_a_813_: *mut lean_object = core::ptr::null_mut(); let mut v___x_814_: usize = 0; let mut v___x_815_: usize = 0; let mut v___y_818_: *mut lean_object = core::ptr::null_mut(); let mut v_a_819_: *mut lean_object = core::ptr::null_mut(); let mut v_a_820_: *mut lean_object = core::ptr::null_mut(); let mut v___x_821_: u8 = 0; let mut v___x_822_: *mut lean_object = core::ptr::null_mut(); let mut v_key_823_: *mut lean_object = core::ptr::null_mut(); let mut v_val_824_: *mut lean_object = core::ptr::null_mut(); let mut v___x_825_: *mut lean_object = core::ptr::null_mut(); let mut v_node_826_: *mut lean_object = core::ptr::null_mut(); let mut v___x_827_: *mut lean_object = core::ptr::null_mut(); let mut v___x_828_: *mut lean_object = core::ptr::null_mut(); let mut v___x_829_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_821_ = lean_usize_dec_eq(v_i_808_, v_stop_809_);
if v___x_821_ == 0 {
let mut v___x_822_: *mut lean_object = core::ptr::null_mut(); 
v___x_822_ = lean_array_uget_borrowed(v_as_807_, v_i_808_);
match lean_obj_tag(v___x_822_)
{
0 => {
let mut v_key_823_: *mut lean_object = core::ptr::null_mut(); let mut v_val_824_: *mut lean_object = core::ptr::null_mut(); let mut v___x_825_: *mut lean_object = core::ptr::null_mut(); 
v_key_823_ = lean_ctor_get(v___x_822_, 0);
v_val_824_ = lean_ctor_get(v___x_822_, 1);
lean_inc_ref(v_f_806_);
lean_inc(v_val_824_);
lean_inc(v_key_823_);
v___x_825_ = lean_apply_4(v_f_806_, v_b_810_, v_key_823_, v_val_824_, lean_box(0));
v___y_818_ = v___x_825_;
state = 2; continue;
}
1 => {
let mut v_node_826_: *mut lean_object = core::ptr::null_mut(); let mut v___x_827_: *mut lean_object = core::ptr::null_mut(); 
v_node_826_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_node_826_);
lean_inc_ref(v_f_806_);
v___x_827_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___redArg(v_f_806_, v_node_826_, v_b_810_);
v___y_818_ = v___x_827_;
state = 2; continue;
}
_ => {
v_a_813_ = v_b_810_;
state = 1; continue;
}
}
} else {
let mut v___x_828_: *mut lean_object = core::ptr::null_mut(); let mut v___x_829_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_f_806_);
v___x_828_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_828_, 0, v_b_810_);
v___x_829_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
1 => {
v___x_814_ = 1usize;
v___x_815_ = lean_usize_add(v_i_808_, v___x_814_);
v_i_808_ = v___x_815_;
v_b_810_ = v_a_813_;
state = 0; continue;
}
2 => {
if lean_obj_tag(v___y_818_) == 0 {
let mut v_a_819_: *mut lean_object = core::ptr::null_mut(); 
v_a_819_ = lean_ctor_get(v___y_818_, 0);
if lean_obj_tag(v_a_819_) == 0 {
lean_dec_ref(v_f_806_);
return v___y_818_;
} else {
let mut v_a_820_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_819_);
lean_dec_ref_known(v___y_818_, 1);
v_a_820_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v_a_819_, 1);
v_a_813_ = v_a_820_;
state = 1; continue;
}
} else {
lean_dec_ref(v_f_806_);
return v___y_818_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3___redArg___boxed(mut v_f_830_: *mut lean_object, mut v_as_831_: *mut lean_object, mut v_i_832_: *mut lean_object, mut v_stop_833_: *mut lean_object, mut v_b_834_: *mut lean_object, mut v___y_835_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_836_: usize = 0; let mut v_stop_boxed_837_: usize = 0; let mut v_res_838_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_836_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_stop_boxed_837_ = lean_unbox_usize(v_stop_833_);
lean_dec(v_stop_833_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3___redArg(v_f_830_, v_as_831_, v_i_boxed_836_, v_stop_boxed_837_, v_b_834_);
lean_dec_ref(v_as_831_);
return v_res_838_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___redArg___boxed(mut v_f_839_: *mut lean_object, mut v_x_840_: *mut lean_object, mut v_x_841_: *mut lean_object, mut v___y_842_: *mut lean_object) -> *mut lean_object{
let mut v_res_843_: *mut lean_object = core::ptr::null_mut(); 
v_res_843_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___redArg(v_f_839_, v_x_840_, v_x_841_);
return v_res_843_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg___lam__0(mut v_f_844_: *mut lean_object, mut v_s_845_: *mut lean_object, mut v_a_846_: u64, mut v_b_847_: *mut lean_object) -> *mut lean_object{
let mut v___x_849_: *mut lean_object = core::ptr::null_mut(); let mut v___x_850_: *mut lean_object = core::ptr::null_mut(); let mut v___x_851_: *mut lean_object = core::ptr::null_mut(); let mut v_a_852_: *mut lean_object = core::ptr::null_mut(); let mut v___x_854_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_855_: u8 = 0; let mut v_a_856_: *mut lean_object = core::ptr::null_mut(); let mut v___x_858_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_859_: u8 = 0; let mut v___x_861_: *mut lean_object = core::ptr::null_mut(); let mut v___x_863_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_864_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_865_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_866_: u8 = 0; let mut v_a_867_: *mut lean_object = core::ptr::null_mut(); let mut v___x_869_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_870_: u8 = 0; let mut v___x_872_: *mut lean_object = core::ptr::null_mut(); let mut v___x_874_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_875_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_876_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_877_: u8 = 0; let mut v_isSharedCheck_878_: u8 = 0; let mut v_a_879_: *mut lean_object = core::ptr::null_mut(); let mut v___x_881_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_882_: u8 = 0; let mut v___x_884_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_885_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_886_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_849_ = lean_box_uint64(v_a_846_);
v___x_850_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v_b_847_);
v___x_851_ = lean_apply_3(v_f_844_, v___x_850_, v_s_845_, lean_box(0));
if lean_obj_tag(v___x_851_) == 0 {
let mut v_a_852_: *mut lean_object = core::ptr::null_mut(); let mut v___x_854_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_855_: u8 = 0; let mut v_isSharedCheck_878_: u8 = 0; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_878_ = (!lean_is_exclusive(v___x_851_)) as u8;
if v_isSharedCheck_878_ == 0 {
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_878_;
state = 1; continue;
} else {
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_878_;
state = 1; continue;
}
} else {
let mut v_a_879_: *mut lean_object = core::ptr::null_mut(); let mut v___x_881_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_882_: u8 = 0; let mut v_isSharedCheck_886_: u8 = 0; 
v_a_879_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_886_ = (!lean_is_exclusive(v___x_851_)) as u8;
if v_isSharedCheck_886_ == 0 {
v___x_881_ = v___x_851_;
v_isShared_882_ = v_isSharedCheck_886_;
state = 8; continue;
} else {
lean_inc(v_a_879_);
lean_dec(v___x_851_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
state = 8; continue;
}
}
}
1 => {
if lean_obj_tag(v_a_852_) == 0 {
let mut v_a_856_: *mut lean_object = core::ptr::null_mut(); let mut v___x_858_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_859_: u8 = 0; let mut v_isSharedCheck_866_: u8 = 0; 
v_a_856_ = lean_ctor_get(v_a_852_, 0);
v_isSharedCheck_866_ = (!lean_is_exclusive(v_a_852_)) as u8;
if v_isSharedCheck_866_ == 0 {
v___x_858_ = v_a_852_;
v_isShared_859_ = v_isSharedCheck_866_;
state = 2; continue;
} else {
lean_inc(v_a_856_);
lean_dec(v_a_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
state = 2; continue;
}
} else {
let mut v_a_867_: *mut lean_object = core::ptr::null_mut(); let mut v___x_869_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_870_: u8 = 0; let mut v_isSharedCheck_877_: u8 = 0; 
v_a_867_ = lean_ctor_get(v_a_852_, 0);
v_isSharedCheck_877_ = (!lean_is_exclusive(v_a_852_)) as u8;
if v_isSharedCheck_877_ == 0 {
v___x_869_ = v_a_852_;
v_isShared_870_ = v_isSharedCheck_877_;
state = 5; continue;
} else {
lean_inc(v_a_867_);
lean_dec(v_a_852_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_877_;
state = 5; continue;
}
}
}
8 => {
if v_isShared_882_ == 0 {
v___x_884_ = v___x_881_;
state = 9; continue;
} else {
let mut v_reuseFailAlloc_885_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
state = 9; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg___lam__0___boxed(mut v_f_887_: *mut lean_object, mut v_s_888_: *mut lean_object, mut v_a_889_: *mut lean_object, mut v_b_890_: *mut lean_object, mut v___y_891_: *mut lean_object) -> *mut lean_object{
let mut v_a_boxed_892_: u64 = 0; let mut v_res_893_: *mut lean_object = core::ptr::null_mut(); 
v_a_boxed_892_ = lean_unbox_uint64(v_a_889_);
lean_dec_ref(v_a_889_);
v_res_893_ = l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg___lam__0(v_f_887_, v_s_888_, v_a_boxed_892_, v_b_890_);
return v_res_893_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg(mut v_map_894_: *mut lean_object, mut v_init_895_: *mut lean_object, mut v_f_896_: *mut lean_object) -> *mut lean_object{
let mut v___f_898_: *mut lean_object = core::ptr::null_mut(); let mut v___x_899_: *mut lean_object = core::ptr::null_mut(); let mut v_a_900_: *mut lean_object = core::ptr::null_mut(); let mut v___x_902_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_903_: u8 = 0; let mut v_a_904_: *mut lean_object = core::ptr::null_mut(); let mut v___x_906_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_907_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_908_: u8 = 0; let mut v_a_909_: *mut lean_object = core::ptr::null_mut(); let mut v___x_911_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_912_: u8 = 0; let mut v___x_914_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_915_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_916_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___f_898_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 1);
lean_closure_set(v___f_898_, 0, v_f_896_);
lean_inc_ref(v_map_894_);
v___x_899_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___redArg(v___f_898_, v_map_894_, v_init_895_);
if lean_obj_tag(v___x_899_) == 0 {
let mut v_a_900_: *mut lean_object = core::ptr::null_mut(); let mut v___x_902_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_903_: u8 = 0; let mut v_isSharedCheck_908_: u8 = 0; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_908_ = (!lean_is_exclusive(v___x_899_)) as u8;
if v_isSharedCheck_908_ == 0 {
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_908_;
state = 1; continue;
} else {
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_908_;
state = 1; continue;
}
} else {
let mut v_a_909_: *mut lean_object = core::ptr::null_mut(); let mut v___x_911_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_912_: u8 = 0; let mut v_isSharedCheck_916_: u8 = 0; 
v_a_909_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_916_ = (!lean_is_exclusive(v___x_899_)) as u8;
if v_isSharedCheck_916_ == 0 {
v___x_911_ = v___x_899_;
v_isShared_912_ = v_isSharedCheck_916_;
state = 3; continue;
} else {
lean_inc(v_a_909_);
lean_dec(v___x_899_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
state = 3; continue;
}
}
}
1 => {
v_a_904_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_a_904_);
lean_dec(v_a_900_);
if v_isShared_903_ == 0 {
lean_ctor_set(v___x_902_, 0, v_a_904_);
v___x_906_ = v___x_902_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_907_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_904_);
v___x_906_ = v_reuseFailAlloc_907_;
state = 2; continue;
}
}
3 => {
if v_isShared_912_ == 0 {
v___x_914_ = v___x_911_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_915_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg___boxed(mut v_map_917_: *mut lean_object, mut v_init_918_: *mut lean_object, mut v_f_919_: *mut lean_object, mut v___y_920_: *mut lean_object) -> *mut lean_object{
let mut v_res_921_: *mut lean_object = core::ptr::null_mut(); 
v_res_921_ = l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg(v_map_917_, v_init_918_, v_f_919_);
lean_dec_ref(v_map_917_);
return v_res_921_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___lam__0(mut v_sum_922_: u64, mut v_x_923_: *mut lean_object, mut v_____s_924_: u64) -> *mut lean_object{
let mut v_fst_926_: *mut lean_object = core::ptr::null_mut(); let mut v___x_927_: u64 = 0; let mut v___x_928_: u64 = 0; let mut v___x_929_: u8 = 0; 
v_fst_926_ = lean_ctor_get(v_x_923_, 0);
v___x_927_ = lean_unbox_uint64(v_fst_926_);
v___x_928_ = lean_uint64_add(v_____s_924_, v___x_927_);
v___x_929_ = lean_uint64_dec_eq(v___x_928_, v_sum_922_);
if v___x_929_ == 0 {
let mut v___x_930_: *mut lean_object = core::ptr::null_mut(); let mut v___x_931_: *mut lean_object = core::ptr::null_mut(); let mut v___x_932_: *mut lean_object = core::ptr::null_mut(); 
v___x_930_ = lean_box_uint64(v___x_928_);
v___x_931_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_931_, 0, v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
} else {
let mut v___x_933_: *mut lean_object = core::ptr::null_mut(); let mut v___x_934_: *mut lean_object = core::ptr::null_mut(); let mut v___x_935_: *mut lean_object = core::ptr::null_mut(); 
v___x_933_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_934_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___x_935_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___lam__0___boxed(mut v_sum_936_: *mut lean_object, mut v_x_937_: *mut lean_object, mut v_____s_938_: *mut lean_object, mut v___y_939_: *mut lean_object) -> *mut lean_object{
let mut v_sum_boxed_940_: u64 = 0; let mut v_____s_2406__boxed_941_: u64 = 0; let mut v_res_942_: *mut lean_object = core::ptr::null_mut(); 
v_sum_boxed_940_ = lean_unbox_uint64(v_sum_936_);
lean_dec_ref(v_sum_936_);
v_____s_2406__boxed_941_ = lean_unbox_uint64(v_____s_938_);
lean_dec_ref(v_____s_938_);
v_res_942_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___lam__0(v_sum_boxed_940_, v_x_937_, v_____s_2406__boxed_941_);
lean_dec_ref(v_x_937_);
return v_res_942_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg(mut v_map_945_: *mut lean_object, mut v_size_946_: *mut lean_object, mut v_a_947_: *mut lean_object) -> *mut lean_object{
let mut v_fst_949_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_950_: *mut lean_object = core::ptr::null_mut(); let mut v___x_952_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_953_: u8 = 0; let mut v___x_954_: *mut lean_object = core::ptr::null_mut(); let mut v___x_955_: u8 = 0; let mut v___x_956_: *mut lean_object = core::ptr::null_mut(); let mut v___f_957_: *mut lean_object = core::ptr::null_mut(); let mut v___x_958_: *mut lean_object = core::ptr::null_mut(); let mut v_a_959_: *mut lean_object = core::ptr::null_mut(); let mut v___x_960_: *mut lean_object = core::ptr::null_mut(); let mut v___x_962_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_964_: *mut lean_object = core::ptr::null_mut(); let mut v_a_965_: *mut lean_object = core::ptr::null_mut(); let mut v___x_967_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_968_: u8 = 0; let mut v___x_970_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_971_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_972_: u8 = 0; let mut v___x_974_: *mut lean_object = core::ptr::null_mut(); let mut v___x_975_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_976_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_977_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_949_ = lean_ctor_get(v_a_947_, 0);
v_snd_950_ = lean_ctor_get(v_a_947_, 1);
v_isSharedCheck_977_ = (!lean_is_exclusive(v_a_947_)) as u8;
if v_isSharedCheck_977_ == 0 {
v___x_952_ = v_a_947_;
v_isShared_953_ = v_isSharedCheck_977_;
state = 1; continue;
} else {
lean_inc(v_snd_950_);
lean_inc(v_fst_949_);
lean_dec(v_a_947_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_977_;
state = 1; continue;
}
}
1 => {
v___x_954_ = lean_unsigned_to_nat(0);
v___x_955_ = lean_nat_dec_eq(v_fst_949_, v___x_954_);
if v___x_955_ == 0 {
let mut v___x_956_: *mut lean_object = core::ptr::null_mut(); let mut v___f_957_: *mut lean_object = core::ptr::null_mut(); let mut v___x_958_: *mut lean_object = core::ptr::null_mut(); 
v___x_956_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___boxed__const__1;
v___f_957_ = lean_alloc_closure(l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
lean_closure_set(v___f_957_, 0, v___x_956_);
v___x_958_ = l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg(v_map_945_, v_snd_950_, v___f_957_);
if lean_obj_tag(v___x_958_) == 0 {
let mut v_a_959_: *mut lean_object = core::ptr::null_mut(); let mut v___x_960_: *mut lean_object = core::ptr::null_mut(); let mut v___x_962_: *mut lean_object = core::ptr::null_mut(); 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = lean_nat_sub(v_fst_949_, v_size_946_);
lean_dec(v_fst_949_);
if v_isShared_953_ == 0 {
lean_ctor_set(v___x_952_, 1, v_a_959_);
lean_ctor_set(v___x_952_, 0, v___x_960_);
v___x_962_ = v___x_952_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_964_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_a_959_);
v___x_962_ = v_reuseFailAlloc_964_;
state = 2; continue;
}
} else {
let mut v_a_965_: *mut lean_object = core::ptr::null_mut(); let mut v___x_967_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_968_: u8 = 0; let mut v_isSharedCheck_972_: u8 = 0; 
lean_del_object(v___x_952_);
lean_dec(v_fst_949_);
v_a_965_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_972_ = (!lean_is_exclusive(v___x_958_)) as u8;
if v_isSharedCheck_972_ == 0 {
v___x_967_ = v___x_958_;
v_isShared_968_ = v_isSharedCheck_972_;
state = 3; continue;
} else {
lean_inc(v_a_965_);
lean_dec(v___x_958_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
state = 3; continue;
}
}
} else {
let mut v___x_974_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_953_ == 0 {
v___x_974_ = v___x_952_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_976_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_fst_949_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_snd_950_);
v___x_974_ = v_reuseFailAlloc_976_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___boxed(mut v_map_978_: *mut lean_object, mut v_size_979_: *mut lean_object, mut v_a_980_: *mut lean_object, mut v___y_981_: *mut lean_object) -> *mut lean_object{
let mut v_res_982_: *mut lean_object = core::ptr::null_mut(); 
v_res_982_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg(v_map_978_, v_size_979_, v_a_980_);
lean_dec(v_size_979_);
lean_dec_ref(v_map_978_);
return v_res_982_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterate___lam__0(mut v_map_983_: *mut lean_object, mut v_size_984_: *mut lean_object, mut v___x_985_: *mut lean_object) -> *mut lean_object{
let mut v___x_987_: *mut lean_object = core::ptr::null_mut(); let mut v___x_989_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_990_: u8 = 0; let mut v___x_991_: *mut lean_object = core::ptr::null_mut(); let mut v___x_993_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_994_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_995_: u8 = 0; let mut v_unused_996_: *mut lean_object = core::ptr::null_mut(); let mut v_a_997_: *mut lean_object = core::ptr::null_mut(); let mut v___x_999_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1000_: u8 = 0; let mut v___x_1002_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1003_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1004_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_987_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg(v_map_983_, v_size_984_, v___x_985_);
if lean_obj_tag(v___x_987_) == 0 {
let mut v___x_989_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_990_: u8 = 0; let mut v_isSharedCheck_995_: u8 = 0; 
v_isSharedCheck_995_ = (!lean_is_exclusive(v___x_987_)) as u8;
if v_isSharedCheck_995_ == 0 {
let mut v_unused_996_: *mut lean_object = core::ptr::null_mut(); 
v_unused_996_ = lean_ctor_get(v___x_987_, 0);
lean_dec(v_unused_996_);
v___x_989_ = v___x_987_;
v_isShared_990_ = v_isSharedCheck_995_;
state = 1; continue;
} else {
lean_dec(v___x_987_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
state = 1; continue;
}
} else {
let mut v_a_997_: *mut lean_object = core::ptr::null_mut(); let mut v___x_999_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1000_: u8 = 0; let mut v_isSharedCheck_1004_: u8 = 0; 
v_a_997_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1004_ = (!lean_is_exclusive(v___x_987_)) as u8;
if v_isSharedCheck_1004_ == 0 {
v___x_999_ = v___x_987_;
v_isShared_1000_ = v_isSharedCheck_1004_;
state = 3; continue;
} else {
lean_inc(v_a_997_);
lean_dec(v___x_987_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
state = 3; continue;
}
}
}
1 => {
v___x_991_ = lean_box(0);
if v_isShared_990_ == 0 {
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_994_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
state = 2; continue;
}
}
3 => {
if v_isShared_1000_ == 0 {
v___x_1002_ = v___x_999_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1003_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterate___lam__0___boxed(mut v_map_1005_: *mut lean_object, mut v_size_1006_: *mut lean_object, mut v___x_1007_: *mut lean_object, mut v___y_1008_: *mut lean_object) -> *mut lean_object{
let mut v_res_1009_: *mut lean_object = core::ptr::null_mut(); 
v_res_1009_ = l_benchIterate___lam__0(v_map_1005_, v_size_1006_, v___x_1007_);
lean_dec(v_size_1006_);
lean_dec_ref(v_map_1005_);
return v_res_1009_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterate(mut v_seed_1010_: u64, mut v_size_1011_: *mut lean_object) -> *mut lean_object{
let mut v_map_1013_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1014_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1015_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1016_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1017_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1018_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1019_: *mut lean_object = core::ptr::null_mut(); 
v_map_1013_ = l_mkMapWithCap(v_seed_1010_, v_size_1011_);
v___x_1014_ = lean_unsigned_to_nat(100);
v_todo_1015_ = lean_nat_mul(v_size_1011_, v___x_1014_);
v___x_1016_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg___boxed__const__1;
lean_inc(v_todo_1015_);
v___x_1017_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1017_, 0, v_todo_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___f_1018_ = lean_alloc_closure(l_benchIterate___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_1018_, 0, v_map_1013_);
lean_closure_set(v___f_1018_, 1, v_size_1011_);
lean_closure_set(v___f_1018_, 2, v___x_1017_);
v___x_1019_ = l_timeNanos(v_todo_1015_, v___f_1018_);
return v___x_1019_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchIterate___boxed(mut v_seed_1020_: *mut lean_object, mut v_size_1021_: *mut lean_object, mut v_a_1022_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1023_: u64 = 0; let mut v_res_1024_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1023_ = lean_unbox_uint64(v_seed_1020_);
lean_dec_ref(v_seed_1020_);
v_res_1024_ = l_benchIterate(v_seed_boxed_1023_, v_size_1021_);
return v_res_1024_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0(mut v_00_u03c3_1025_: *mut lean_object, mut v_00_u03b2_1026_: *mut lean_object, mut v_map_1027_: *mut lean_object, mut v_init_1028_: *mut lean_object, mut v_f_1029_: *mut lean_object) -> *mut lean_object{
let mut v___x_1031_: *mut lean_object = core::ptr::null_mut(); 
v___x_1031_ = l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___redArg(v_map_1027_, v_init_1028_, v_f_1029_);
return v___x_1031_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0___boxed(mut v_00_u03c3_1032_: *mut lean_object, mut v_00_u03b2_1033_: *mut lean_object, mut v_map_1034_: *mut lean_object, mut v_init_1035_: *mut lean_object, mut v_f_1036_: *mut lean_object, mut v___y_1037_: *mut lean_object) -> *mut lean_object{
let mut v_res_1038_: *mut lean_object = core::ptr::null_mut(); 
v_res_1038_ = l_Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0(v_00_u03c3_1032_, v_00_u03b2_1033_, v_map_1034_, v_init_1035_, v_f_1036_);
lean_dec_ref(v_map_1034_);
return v_res_1038_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1(mut v_map_1039_: *mut lean_object, mut v_size_1040_: *mut lean_object, mut v_inst_1041_: *mut lean_object, mut v_a_1042_: *mut lean_object) -> *mut lean_object{
let mut v___x_1044_: *mut lean_object = core::ptr::null_mut(); 
v___x_1044_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___redArg(v_map_1039_, v_size_1040_, v_a_1042_);
return v___x_1044_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1___boxed(mut v_map_1045_: *mut lean_object, mut v_size_1046_: *mut lean_object, mut v_inst_1047_: *mut lean_object, mut v_a_1048_: *mut lean_object, mut v___y_1049_: *mut lean_object) -> *mut lean_object{
let mut v_res_1050_: *mut lean_object = core::ptr::null_mut(); 
v_res_1050_ = l___private_Init_While_0__whileM_erased___at___00benchIterate_spec__1(v_map_1045_, v_size_1046_, v_inst_1047_, v_a_1048_);
lean_dec(v_size_1046_);
lean_dec_ref(v_map_1045_);
return v_res_1050_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0___redArg(mut v_map_1051_: *mut lean_object, mut v_f_1052_: *mut lean_object, mut v_init_1053_: *mut lean_object) -> *mut lean_object{
let mut v___x_1055_: *mut lean_object = core::ptr::null_mut(); 
v___x_1055_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___redArg(v_f_1052_, v_map_1051_, v_init_1053_);
return v___x_1055_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0___redArg___boxed(mut v_map_1056_: *mut lean_object, mut v_f_1057_: *mut lean_object, mut v_init_1058_: *mut lean_object, mut v___y_1059_: *mut lean_object) -> *mut lean_object{
let mut v_res_1060_: *mut lean_object = core::ptr::null_mut(); 
v_res_1060_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0___redArg(v_map_1056_, v_f_1057_, v_init_1058_);
return v_res_1060_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0(mut v_00_u03c3_1061_: *mut lean_object, mut v_00_u03c3_1062_: *mut lean_object, mut v_00_u03b2_1063_: *mut lean_object, mut v_map_1064_: *mut lean_object, mut v_f_1065_: *mut lean_object, mut v_init_1066_: *mut lean_object) -> *mut lean_object{
let mut v___x_1068_: *mut lean_object = core::ptr::null_mut(); 
v___x_1068_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___redArg(v_f_1065_, v_map_1064_, v_init_1066_);
return v___x_1068_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0___boxed(mut v_00_u03c3_1069_: *mut lean_object, mut v_00_u03c3_1070_: *mut lean_object, mut v_00_u03b2_1071_: *mut lean_object, mut v_map_1072_: *mut lean_object, mut v_f_1073_: *mut lean_object, mut v_init_1074_: *mut lean_object, mut v___y_1075_: *mut lean_object) -> *mut lean_object{
let mut v_res_1076_: *mut lean_object = core::ptr::null_mut(); 
v_res_1076_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0(v_00_u03c3_1069_, v_00_u03c3_1070_, v_00_u03b2_1071_, v_map_1072_, v_f_1073_, v_init_1074_);
return v_res_1076_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1(mut v_00_u03c3_1077_: *mut lean_object, mut v_00_u03c3_1078_: *mut lean_object, mut v_00_u03b1_1079_: *mut lean_object, mut v_00_u03b2_1080_: *mut lean_object, mut v_f_1081_: *mut lean_object, mut v_x_1082_: *mut lean_object, mut v_x_1083_: *mut lean_object) -> *mut lean_object{
let mut v___x_1085_: *mut lean_object = core::ptr::null_mut(); 
v___x_1085_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___redArg(v_f_1081_, v_x_1082_, v_x_1083_);
return v___x_1085_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1___boxed(mut v_00_u03c3_1086_: *mut lean_object, mut v_00_u03c3_1087_: *mut lean_object, mut v_00_u03b1_1088_: *mut lean_object, mut v_00_u03b2_1089_: *mut lean_object, mut v_f_1090_: *mut lean_object, mut v_x_1091_: *mut lean_object, mut v_x_1092_: *mut lean_object, mut v___y_1093_: *mut lean_object) -> *mut lean_object{
let mut v_res_1094_: *mut lean_object = core::ptr::null_mut(); 
v_res_1094_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1(v_00_u03c3_1086_, v_00_u03c3_1087_, v_00_u03b1_1088_, v_00_u03b2_1089_, v_f_1090_, v_x_1091_, v_x_1092_);
return v_res_1094_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3(mut v_00_u03b1_1095_: *mut lean_object, mut v_00_u03b2_1096_: *mut lean_object, mut v_00_u03c3_1097_: *mut lean_object, mut v_00_u03c3_1098_: *mut lean_object, mut v_f_1099_: *mut lean_object, mut v_as_1100_: *mut lean_object, mut v_i_1101_: usize, mut v_stop_1102_: usize, mut v_b_1103_: *mut lean_object) -> *mut lean_object{
let mut v___x_1105_: *mut lean_object = core::ptr::null_mut(); 
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1099_, v_as_1100_, v_i_1101_, v_stop_1102_, v_b_1103_);
return v___x_1105_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3___boxed(mut v_00_u03b1_1106_: *mut lean_object, mut v_00_u03b2_1107_: *mut lean_object, mut v_00_u03c3_1108_: *mut lean_object, mut v_00_u03c3_1109_: *mut lean_object, mut v_f_1110_: *mut lean_object, mut v_as_1111_: *mut lean_object, mut v_i_1112_: *mut lean_object, mut v_stop_1113_: *mut lean_object, mut v_b_1114_: *mut lean_object, mut v___y_1115_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_1116_: usize = 0; let mut v_stop_boxed_1117_: usize = 0; let mut v_res_1118_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_1116_ = lean_unbox_usize(v_i_1112_);
lean_dec(v_i_1112_);
v_stop_boxed_1117_ = lean_unbox_usize(v_stop_1113_);
lean_dec(v_stop_1113_);
v_res_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1106_, v_00_u03b2_1107_, v_00_u03c3_1108_, v_00_u03c3_1109_, v_f_1110_, v_as_1111_, v_i_boxed_1116_, v_stop_boxed_1117_, v_b_1114_);
lean_dec_ref(v_as_1111_);
return v_res_1118_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__4(mut v_00_u03c3_1119_: *mut lean_object, mut v_00_u03c3_1120_: *mut lean_object, mut v_00_u03b1_1121_: *mut lean_object, mut v_00_u03b2_1122_: *mut lean_object, mut v_f_1123_: *mut lean_object, mut v_keys_1124_: *mut lean_object, mut v_vals_1125_: *mut lean_object, mut v_heq_1126_: *mut lean_object, mut v_i_1127_: *mut lean_object, mut v_acc_1128_: *mut lean_object) -> *mut lean_object{
let mut v___x_1130_: *mut lean_object = core::ptr::null_mut(); 
v___x_1130_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__4___redArg(v_f_1123_, v_keys_1124_, v_vals_1125_, v_i_1127_, v_acc_1128_);
return v___x_1130_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__4___boxed(mut v_00_u03c3_1131_: *mut lean_object, mut v_00_u03c3_1132_: *mut lean_object, mut v_00_u03b1_1133_: *mut lean_object, mut v_00_u03b2_1134_: *mut lean_object, mut v_f_1135_: *mut lean_object, mut v_keys_1136_: *mut lean_object, mut v_vals_1137_: *mut lean_object, mut v_heq_1138_: *mut lean_object, mut v_i_1139_: *mut lean_object, mut v_acc_1140_: *mut lean_object, mut v___y_1141_: *mut lean_object) -> *mut lean_object{
let mut v_res_1142_: *mut lean_object = core::ptr::null_mut(); 
v_res_1142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00benchIterate_spec__0_spec__0_spec__1_spec__4(v_00_u03c3_1131_, v_00_u03c3_1132_, v_00_u03b1_1133_, v_00_u03b2_1134_, v_f_1135_, v_keys_1136_, v_vals_1137_, v_heq_1138_, v_i_1139_, v_acc_1140_);
lean_dec_ref(v_vals_1137_);
lean_dec_ref(v_keys_1136_);
return v_res_1142_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_isEmpty___at___00benchInsertHit_spec__0___redArg(mut v_x_1143_: *mut lean_object) -> u8{
let mut v___x_1144_: u8 = 0; 
v___x_1144_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1143_);
return v___x_1144_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_isEmpty___at___00benchInsertHit_spec__0___redArg___boxed(mut v_x_1145_: *mut lean_object) -> *mut lean_object{
let mut v_res_1146_: u8 = 0; let mut v_r_1147_: *mut lean_object = core::ptr::null_mut(); 
v_res_1146_ = l_Lean_PersistentHashMap_isEmpty___at___00benchInsertHit_spec__0___redArg(v_x_1145_);
lean_dec_ref(v_x_1145_);
v_r_1147_ = lean_box((v_res_1146_) as usize);
return v_r_1147_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_isEmpty___at___00benchInsertHit_spec__0(mut v_00_u03b2_1148_: *mut lean_object, mut v_x_1149_: *mut lean_object) -> u8{
let mut v___x_1150_: u8 = 0; 
v___x_1150_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1149_);
return v___x_1150_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_isEmpty___at___00benchInsertHit_spec__0___boxed(mut v_00_u03b2_1151_: *mut lean_object, mut v_x_1152_: *mut lean_object) -> *mut lean_object{
let mut v_res_1153_: u8 = 0; let mut v_r_1154_: *mut lean_object = core::ptr::null_mut(); 
v_res_1153_ = l_Lean_PersistentHashMap_isEmpty___at___00benchInsertHit_spec__0(v_00_u03b2_1151_, v_x_1152_);
lean_dec_ref(v_x_1152_);
v_r_1154_ = lean_box((v_res_1153_) as usize);
return v_r_1154_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1___redArg(mut v_a_1155_: *mut lean_object, mut v_b_1156_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_1158_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_1159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1161_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1162_: u8 = 0; let mut v___x_1163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1164_: u8 = 0; let mut v___x_1165_: u64 = 0; let mut v___x_1166_: u64 = 0; let mut v___x_1167_: u64 = 0; let mut v___x_1168_: u64 = 0; let mut v___x_1169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1170_: u8 = 0; let mut v___x_1171_: u64 = 0; let mut v___x_1172_: u64 = 0; let mut v___x_1173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1176_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1178_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1181_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1182_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1183_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_1158_ = lean_ctor_get(v_a_1155_, 0);
v_inner_1159_ = lean_ctor_get(v_a_1155_, 1);
v_isSharedCheck_1183_ = (!lean_is_exclusive(v_a_1155_)) as u8;
if v_isSharedCheck_1183_ == 0 {
v___x_1161_ = v_a_1155_;
v_isShared_1162_ = v_isSharedCheck_1183_;
state = 1; continue;
} else {
lean_inc(v_inner_1159_);
lean_inc(v_countdown_1158_);
lean_dec(v_a_1155_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1183_;
state = 1; continue;
}
}
1 => {
v___x_1163_ = lean_unsigned_to_nat(1);
v___x_1164_ = lean_nat_dec_eq(v_countdown_1158_, v___x_1163_);
if v___x_1164_ == 0 {
let mut v___x_1165_: u64 = 0; let mut v___x_1166_: u64 = 0; let mut v___x_1167_: u64 = 0; let mut v___x_1168_: u64 = 0; let mut v___x_1169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1170_: u8 = 0; 
v___x_1165_ = 1u64;
v___x_1166_ = lean_unbox_uint64(v_inner_1159_);
v___x_1167_ = lean_uint64_add(v___x_1166_, v___x_1165_);
v___x_1168_ = lean_unbox_uint64(v_inner_1159_);
v___x_1169_ = l_Lean_PersistentHashMap_insert___at___00mkMapWithCap_spec__0___redArg(v_b_1156_, v___x_1168_, v_inner_1159_);
v___x_1170_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v___x_1169_);
if v___x_1170_ == 0 {
let mut v___x_1171_: u64 = 0; let mut v___x_1172_: u64 = 0; let mut v___x_1173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1176_: *mut lean_object = core::ptr::null_mut(); 
v___x_1171_ = 3787392781u64;
v___x_1172_ = lean_uint64_mul(v___x_1167_, v___x_1171_);
v___x_1173_ = lean_nat_sub(v_countdown_1158_, v___x_1163_);
lean_dec(v_countdown_1158_);
v___x_1174_ = lean_box_uint64(v___x_1172_);
if v_isShared_1162_ == 0 {
lean_ctor_set(v___x_1161_, 1, v___x_1174_);
lean_ctor_set(v___x_1161_, 0, v___x_1173_);
v___x_1176_ = v___x_1161_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1178_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1178_;
state = 2; continue;
}
} else {
let mut v___x_1179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1181_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v___x_1169_);
lean_del_object(v___x_1161_);
lean_dec(v_countdown_1158_);
v___x_1179_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_1180_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
} else {
let mut v___x_1182_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_1161_);
lean_dec(v_inner_1159_);
lean_dec(v_countdown_1158_);
v___x_1182_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1182_, 0, v_b_1156_);
return v___x_1182_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1___redArg___boxed(mut v_a_1184_: *mut lean_object, mut v_b_1185_: *mut lean_object, mut v___y_1186_: *mut lean_object) -> *mut lean_object{
let mut v_res_1187_: *mut lean_object = core::ptr::null_mut(); 
v_res_1187_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1___redArg(v_a_1184_, v_b_1185_);
return v_res_1187_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__2___redArg(mut v_seed_1188_: u64, mut v_size_1189_: *mut lean_object, mut v_a_1190_: *mut lean_object) -> *mut lean_object{
let mut v_fst_1192_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1193_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1195_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1196_: u8 = 0; let mut v___x_1197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1198_: u8 = 0; let mut v___x_1199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1203_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1207_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1209_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1212_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1213_: u8 = 0; let mut v___x_1215_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1216_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1217_: u8 = 0; let mut v___x_1219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1220_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1221_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1222_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_1192_ = lean_ctor_get(v_a_1190_, 0);
v_snd_1193_ = lean_ctor_get(v_a_1190_, 1);
v_isSharedCheck_1222_ = (!lean_is_exclusive(v_a_1190_)) as u8;
if v_isSharedCheck_1222_ == 0 {
v___x_1195_ = v_a_1190_;
v_isShared_1196_ = v_isSharedCheck_1222_;
state = 1; continue;
} else {
lean_inc(v_snd_1193_);
lean_inc(v_fst_1192_);
lean_dec(v_a_1190_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1222_;
state = 1; continue;
}
}
1 => {
v___x_1197_ = lean_unsigned_to_nat(0);
v___x_1198_ = lean_nat_dec_eq(v_fst_1192_, v___x_1197_);
if v___x_1198_ == 0 {
let mut v___x_1199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1203_: *mut lean_object = core::ptr::null_mut(); 
v___x_1199_ = lean_unsigned_to_nat(1);
v___x_1200_ = lean_nat_add(v_size_1189_, v___x_1199_);
v___x_1201_ = lean_box_uint64(v_seed_1188_);
v___x_1202_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1___redArg(v___x_1202_, v_snd_1193_);
if lean_obj_tag(v___x_1203_) == 0 {
let mut v_a_1204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1207_: *mut lean_object = core::ptr::null_mut(); 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1203_, 1);
v___x_1205_ = lean_nat_sub(v_fst_1192_, v_size_1189_);
lean_dec(v_fst_1192_);
if v_isShared_1196_ == 0 {
lean_ctor_set(v___x_1195_, 1, v_a_1204_);
lean_ctor_set(v___x_1195_, 0, v___x_1205_);
v___x_1207_ = v___x_1195_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1209_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_a_1204_);
v___x_1207_ = v_reuseFailAlloc_1209_;
state = 2; continue;
}
} else {
let mut v_a_1210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1212_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1213_: u8 = 0; let mut v_isSharedCheck_1217_: u8 = 0; 
lean_del_object(v___x_1195_);
lean_dec(v_fst_1192_);
v_a_1210_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1217_ = (!lean_is_exclusive(v___x_1203_)) as u8;
if v_isSharedCheck_1217_ == 0 {
v___x_1212_ = v___x_1203_;
v_isShared_1213_ = v_isSharedCheck_1217_;
state = 3; continue;
} else {
lean_inc(v_a_1210_);
lean_dec(v___x_1203_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
state = 3; continue;
}
}
} else {
let mut v___x_1219_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_1196_ == 0 {
v___x_1219_ = v___x_1195_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_1221_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_fst_1192_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_snd_1193_);
v___x_1219_ = v_reuseFailAlloc_1221_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__2___redArg___boxed(mut v_seed_1223_: *mut lean_object, mut v_size_1224_: *mut lean_object, mut v_a_1225_: *mut lean_object, mut v___y_1226_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1227_: u64 = 0; let mut v_res_1228_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1227_ = lean_unbox_uint64(v_seed_1223_);
lean_dec_ref(v_seed_1223_);
v_res_1228_ = l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__2___redArg(v_seed_boxed_1227_, v_size_1224_, v_a_1225_);
lean_dec(v_size_1224_);
return v_res_1228_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertHit___lam__0(mut v_seed_1229_: u64, mut v_size_1230_: *mut lean_object, mut v___x_1231_: *mut lean_object) -> *mut lean_object{
let mut v___x_1233_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1235_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1236_: u8 = 0; let mut v___x_1237_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1239_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1240_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1241_: u8 = 0; let mut v_unused_1242_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1245_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1246_: u8 = 0; let mut v___x_1248_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1249_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1250_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1233_ = l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__2___redArg(v_seed_1229_, v_size_1230_, v___x_1231_);
if lean_obj_tag(v___x_1233_) == 0 {
let mut v___x_1235_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1236_: u8 = 0; let mut v_isSharedCheck_1241_: u8 = 0; 
v_isSharedCheck_1241_ = (!lean_is_exclusive(v___x_1233_)) as u8;
if v_isSharedCheck_1241_ == 0 {
let mut v_unused_1242_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1242_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1242_);
v___x_1235_ = v___x_1233_;
v_isShared_1236_ = v_isSharedCheck_1241_;
state = 1; continue;
} else {
lean_dec(v___x_1233_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1241_;
state = 1; continue;
}
} else {
let mut v_a_1243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1245_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1246_: u8 = 0; let mut v_isSharedCheck_1250_: u8 = 0; 
v_a_1243_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1250_ = (!lean_is_exclusive(v___x_1233_)) as u8;
if v_isSharedCheck_1250_ == 0 {
v___x_1245_ = v___x_1233_;
v_isShared_1246_ = v_isSharedCheck_1250_;
state = 3; continue;
} else {
lean_inc(v_a_1243_);
lean_dec(v___x_1233_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
state = 3; continue;
}
}
}
1 => {
v___x_1237_ = lean_box(0);
if v_isShared_1236_ == 0 {
lean_ctor_set(v___x_1235_, 0, v___x_1237_);
v___x_1239_ = v___x_1235_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1240_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
state = 2; continue;
}
}
3 => {
if v_isShared_1246_ == 0 {
v___x_1248_ = v___x_1245_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1249_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertHit___lam__0___boxed(mut v_seed_1251_: *mut lean_object, mut v_size_1252_: *mut lean_object, mut v___x_1253_: *mut lean_object, mut v___y_1254_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1255_: u64 = 0; let mut v_res_1256_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1255_ = lean_unbox_uint64(v_seed_1251_);
lean_dec_ref(v_seed_1251_);
v_res_1256_ = l_benchInsertHit___lam__0(v_seed_boxed_1255_, v_size_1252_, v___x_1253_);
lean_dec(v_size_1252_);
return v_res_1256_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertHit(mut v_seed_1257_: u64, mut v_size_1258_: *mut lean_object) -> *mut lean_object{
let mut v_map_1260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1261_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1264_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1266_: *mut lean_object = core::ptr::null_mut(); 
v_map_1260_ = l_mkMapWithCap(v_seed_1257_, v_size_1258_);
v___x_1261_ = lean_unsigned_to_nat(100);
v_todo_1262_ = lean_nat_mul(v_size_1258_, v___x_1261_);
lean_inc(v_todo_1262_);
v___x_1263_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1263_, 0, v_todo_1262_);
lean_ctor_set(v___x_1263_, 1, v_map_1260_);
v___x_1264_ = lean_box_uint64(v_seed_1257_);
v___f_1265_ = lean_alloc_closure(l_benchInsertHit___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_1265_, 0, v___x_1264_);
lean_closure_set(v___f_1265_, 1, v_size_1258_);
lean_closure_set(v___f_1265_, 2, v___x_1263_);
v___x_1266_ = l_timeNanos(v_todo_1262_, v___f_1265_);
return v___x_1266_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertHit___boxed(mut v_seed_1267_: *mut lean_object, mut v_size_1268_: *mut lean_object, mut v_a_1269_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1270_: u64 = 0; let mut v_res_1271_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1270_ = lean_unbox_uint64(v_seed_1267_);
lean_dec_ref(v_seed_1267_);
v_res_1271_ = l_benchInsertHit(v_seed_boxed_1270_, v_size_1268_);
return v_res_1271_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1(mut v_inst_1272_: *mut lean_object, mut v_R_1273_: *mut lean_object, mut v_a_1274_: *mut lean_object, mut v_b_1275_: *mut lean_object, mut v_c_1276_: *mut lean_object) -> *mut lean_object{
let mut v___x_1278_: *mut lean_object = core::ptr::null_mut(); 
v___x_1278_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1___redArg(v_a_1274_, v_b_1275_);
return v___x_1278_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1___boxed(mut v_inst_1279_: *mut lean_object, mut v_R_1280_: *mut lean_object, mut v_a_1281_: *mut lean_object, mut v_b_1282_: *mut lean_object, mut v_c_1283_: *mut lean_object, mut v___y_1284_: *mut lean_object) -> *mut lean_object{
let mut v_res_1285_: *mut lean_object = core::ptr::null_mut(); 
v_res_1285_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1(v_inst_1279_, v_R_1280_, v_a_1281_, v_b_1282_, v_c_1283_);
return v_res_1285_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__2(mut v_seed_1286_: u64, mut v_size_1287_: *mut lean_object, mut v_inst_1288_: *mut lean_object, mut v_a_1289_: *mut lean_object) -> *mut lean_object{
let mut v___x_1291_: *mut lean_object = core::ptr::null_mut(); 
v___x_1291_ = l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__2___redArg(v_seed_1286_, v_size_1287_, v_a_1289_);
return v___x_1291_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__2___boxed(mut v_seed_1292_: *mut lean_object, mut v_size_1293_: *mut lean_object, mut v_inst_1294_: *mut lean_object, mut v_a_1295_: *mut lean_object, mut v___y_1296_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1297_: u64 = 0; let mut v_res_1298_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1297_ = lean_unbox_uint64(v_seed_1292_);
lean_dec_ref(v_seed_1292_);
v_res_1298_ = l___private_Init_While_0__whileM_erased___at___00benchInsertHit_spec__2(v_seed_boxed_1297_, v_size_1293_, v_inst_1294_, v_a_1295_);
lean_dec(v_size_1293_);
return v_res_1298_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__0___redArg(mut v_seed_1299_: u64, mut v_size_1300_: *mut lean_object, mut v_a_1301_: *mut lean_object) -> *mut lean_object{
let mut v___x_1303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1304_: u8 = 0; let mut v___x_1305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1306_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1307_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1308_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1312_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1314_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1316_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1317_: u8 = 0; let mut v___x_1319_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1320_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1321_: u8 = 0; let mut v___x_1322_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1303_ = lean_unsigned_to_nat(0);
v___x_1304_ = lean_nat_dec_eq(v_a_1301_, v___x_1303_);
if v___x_1304_ == 0 {
let mut v___x_1305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1306_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1307_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1308_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1309_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1311_: *mut lean_object = core::ptr::null_mut(); 
v___x_1305_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
v___x_1306_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
v___x_1307_ = lean_unsigned_to_nat(1);
v___x_1308_ = lean_nat_add(v_size_1300_, v___x_1307_);
v___x_1309_ = lean_box_uint64(v_seed_1299_);
v___x_1310_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertHit_spec__1___redArg(v___x_1310_, v___x_1306_);
if lean_obj_tag(v___x_1311_) == 0 {
let mut v___x_1312_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1311_, 1);
v___x_1312_ = lean_nat_sub(v_a_1301_, v_size_1300_);
lean_dec(v_a_1301_);
v_a_1301_ = v___x_1312_;
state = 0; continue;
} else {
let mut v_a_1314_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1316_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1317_: u8 = 0; let mut v_isSharedCheck_1321_: u8 = 0; 
lean_dec(v_a_1301_);
v_a_1314_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1321_ = (!lean_is_exclusive(v___x_1311_)) as u8;
if v_isSharedCheck_1321_ == 0 {
v___x_1316_ = v___x_1311_;
v_isShared_1317_ = v_isSharedCheck_1321_;
state = 1; continue;
} else {
lean_inc(v_a_1314_);
lean_dec(v___x_1311_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
state = 1; continue;
}
}
} else {
let mut v___x_1322_: *mut lean_object = core::ptr::null_mut(); 
v___x_1322_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1322_, 0, v_a_1301_);
return v___x_1322_;
}
}
1 => {
if v_isShared_1317_ == 0 {
v___x_1319_ = v___x_1316_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1320_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__0___redArg___boxed(mut v_seed_1323_: *mut lean_object, mut v_size_1324_: *mut lean_object, mut v_a_1325_: *mut lean_object, mut v___y_1326_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1327_: u64 = 0; let mut v_res_1328_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1327_ = lean_unbox_uint64(v_seed_1323_);
lean_dec_ref(v_seed_1323_);
v_res_1328_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__0___redArg(v_seed_boxed_1327_, v_size_1324_, v_a_1325_);
lean_dec(v_size_1324_);
return v_res_1328_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmpty___lam__0(mut v_seed_1329_: u64, mut v_size_1330_: *mut lean_object, mut v_todo_1331_: *mut lean_object) -> *mut lean_object{
let mut v___x_1333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1335_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1336_: u8 = 0; let mut v___x_1337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1339_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1340_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1341_: u8 = 0; let mut v_unused_1342_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1345_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1346_: u8 = 0; let mut v___x_1348_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1349_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1350_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1333_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__0___redArg(v_seed_1329_, v_size_1330_, v_todo_1331_);
if lean_obj_tag(v___x_1333_) == 0 {
let mut v___x_1335_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1336_: u8 = 0; let mut v_isSharedCheck_1341_: u8 = 0; 
v_isSharedCheck_1341_ = (!lean_is_exclusive(v___x_1333_)) as u8;
if v_isSharedCheck_1341_ == 0 {
let mut v_unused_1342_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1342_ = lean_ctor_get(v___x_1333_, 0);
lean_dec(v_unused_1342_);
v___x_1335_ = v___x_1333_;
v_isShared_1336_ = v_isSharedCheck_1341_;
state = 1; continue;
} else {
lean_dec(v___x_1333_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
state = 1; continue;
}
} else {
let mut v_a_1343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1345_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1346_: u8 = 0; let mut v_isSharedCheck_1350_: u8 = 0; 
v_a_1343_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1350_ = (!lean_is_exclusive(v___x_1333_)) as u8;
if v_isSharedCheck_1350_ == 0 {
v___x_1345_ = v___x_1333_;
v_isShared_1346_ = v_isSharedCheck_1350_;
state = 3; continue;
} else {
lean_inc(v_a_1343_);
lean_dec(v___x_1333_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
state = 3; continue;
}
}
}
1 => {
v___x_1337_ = lean_box(0);
if v_isShared_1336_ == 0 {
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1339_ = v___x_1335_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1340_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
state = 2; continue;
}
}
3 => {
if v_isShared_1346_ == 0 {
v___x_1348_ = v___x_1345_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1349_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmpty___lam__0___boxed(mut v_seed_1351_: *mut lean_object, mut v_size_1352_: *mut lean_object, mut v_todo_1353_: *mut lean_object, mut v___y_1354_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1355_: u64 = 0; let mut v_res_1356_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1355_ = lean_unbox_uint64(v_seed_1351_);
lean_dec_ref(v_seed_1351_);
v_res_1356_ = l_benchInsertMissEmpty___lam__0(v_seed_boxed_1355_, v_size_1352_, v_todo_1353_);
lean_dec(v_size_1352_);
return v_res_1356_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmpty(mut v_seed_1357_: u64, mut v_size_1358_: *mut lean_object) -> *mut lean_object{
let mut v___x_1360_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1361_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1362_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1363_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1364_: *mut lean_object = core::ptr::null_mut(); 
v___x_1360_ = lean_unsigned_to_nat(100);
v_todo_1361_ = lean_nat_mul(v_size_1358_, v___x_1360_);
v___x_1362_ = lean_box_uint64(v_seed_1357_);
lean_inc(v_todo_1361_);
v___f_1363_ = lean_alloc_closure(l_benchInsertMissEmpty___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_1363_, 0, v___x_1362_);
lean_closure_set(v___f_1363_, 1, v_size_1358_);
lean_closure_set(v___f_1363_, 2, v_todo_1361_);
v___x_1364_ = l_timeNanos(v_todo_1361_, v___f_1363_);
return v___x_1364_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmpty___boxed(mut v_seed_1365_: *mut lean_object, mut v_size_1366_: *mut lean_object, mut v_a_1367_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1368_: u64 = 0; let mut v_res_1369_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1368_ = lean_unbox_uint64(v_seed_1365_);
lean_dec_ref(v_seed_1365_);
v_res_1369_ = l_benchInsertMissEmpty(v_seed_boxed_1368_, v_size_1366_);
return v_res_1369_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__0(mut v_seed_1370_: u64, mut v_size_1371_: *mut lean_object, mut v_inst_1372_: *mut lean_object, mut v_a_1373_: *mut lean_object) -> *mut lean_object{
let mut v___x_1375_: *mut lean_object = core::ptr::null_mut(); 
v___x_1375_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__0___redArg(v_seed_1370_, v_size_1371_, v_a_1373_);
return v___x_1375_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__0___boxed(mut v_seed_1376_: *mut lean_object, mut v_size_1377_: *mut lean_object, mut v_inst_1378_: *mut lean_object, mut v_a_1379_: *mut lean_object, mut v___y_1380_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1381_: u64 = 0; let mut v_res_1382_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1381_ = lean_unbox_uint64(v_seed_1376_);
lean_dec_ref(v_seed_1376_);
v_res_1382_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmpty_spec__0(v_seed_boxed_1381_, v_size_1377_, v_inst_1378_, v_a_1379_);
lean_dec(v_size_1377_);
return v_res_1382_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmptyShared_spec__0___redArg(mut v_a_1383_: *mut lean_object, mut v_b_1384_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_1386_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_1387_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1389_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1390_: u8 = 0; let mut v___x_1391_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1392_: u8 = 0; let mut v_fst_1393_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1396_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1397_: u8 = 0; let mut v___x_1398_: u64 = 0; let mut v___x_1399_: u64 = 0; let mut v___x_1400_: u64 = 0; let mut v___x_1401_: u64 = 0; let mut v___x_1402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1403_: u8 = 0; let mut v___x_1404_: u64 = 0; let mut v___x_1405_: u64 = 0; let mut v___x_1406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1409_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1410_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1412_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1414_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1415_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1416_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1417_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1418_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1419_: u8 = 0; let mut v___x_1420_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1421_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_1386_ = lean_ctor_get(v_a_1383_, 0);
v_inner_1387_ = lean_ctor_get(v_a_1383_, 1);
v_isSharedCheck_1421_ = (!lean_is_exclusive(v_a_1383_)) as u8;
if v_isSharedCheck_1421_ == 0 {
v___x_1389_ = v_a_1383_;
v_isShared_1390_ = v_isSharedCheck_1421_;
state = 1; continue;
} else {
lean_inc(v_inner_1387_);
lean_inc(v_countdown_1386_);
lean_dec(v_a_1383_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1421_;
state = 1; continue;
}
}
1 => {
v___x_1391_ = lean_unsigned_to_nat(1);
v___x_1392_ = lean_nat_dec_eq(v_countdown_1386_, v___x_1391_);
if v___x_1392_ == 0 {
let mut v_fst_1393_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1396_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1397_: u8 = 0; let mut v_isSharedCheck_1419_: u8 = 0; 
v_fst_1393_ = lean_ctor_get(v_b_1384_, 0);
v_snd_1394_ = lean_ctor_get(v_b_1384_, 1);
v_isSharedCheck_1419_ = (!lean_is_exclusive(v_b_1384_)) as u8;
if v_isSharedCheck_1419_ == 0 {
v___x_1396_ = v_b_1384_;
v_isShared_1397_ = v_isSharedCheck_1419_;
state = 2; continue;
} else {
lean_inc(v_snd_1394_);
lean_inc(v_fst_1393_);
lean_dec(v_b_1384_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1419_;
state = 2; continue;
}
} else {
let mut v___x_1420_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_1389_);
lean_dec(v_inner_1387_);
lean_dec(v_countdown_1386_);
v___x_1420_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1420_, 0, v_b_1384_);
return v___x_1420_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmptyShared_spec__0___redArg___boxed(mut v_a_1422_: *mut lean_object, mut v_b_1423_: *mut lean_object, mut v___y_1424_: *mut lean_object) -> *mut lean_object{
let mut v_res_1425_: *mut lean_object = core::ptr::null_mut(); 
v_res_1425_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmptyShared_spec__0___redArg(v_a_1422_, v_b_1423_);
return v_res_1425_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyShared_spec__1___redArg(mut v_size_1426_: *mut lean_object, mut v_seed_1427_: u64, mut v_a_1428_: *mut lean_object) -> *mut lean_object{
let mut v___x_1430_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1431_: u8 = 0; let mut v___x_1432_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1433_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1436_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1437_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1438_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1439_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1440_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1443_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1444_: u8 = 0; let mut v_snd_1445_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1447_: u8 = 0; let mut v___x_1448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1451_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1453_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1455_: u8 = 0; let mut v_a_1456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1458_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1459_: u8 = 0; let mut v___x_1461_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1462_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1463_: u8 = 0; let mut v___x_1464_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1430_ = lean_unsigned_to_nat(0);
v___x_1431_ = lean_nat_dec_eq(v_a_1428_, v___x_1430_);
if v___x_1431_ == 0 {
let mut v___x_1432_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1433_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1436_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1437_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1438_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1439_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1440_: *mut lean_object = core::ptr::null_mut(); 
v___x_1432_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
v___x_1433_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
v___x_1434_ = lean_mk_empty_array_with_capacity(v_size_1426_);
v___x_1435_ = lean_unsigned_to_nat(1);
v___x_1436_ = lean_nat_add(v_size_1426_, v___x_1435_);
v___x_1437_ = lean_box_uint64(v_seed_1427_);
v___x_1438_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1439_, 0, v___x_1433_);
lean_ctor_set(v___x_1439_, 1, v___x_1434_);
v___x_1440_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmptyShared_spec__0___redArg(v___x_1438_, v___x_1439_);
if lean_obj_tag(v___x_1440_) == 0 {
let mut v_a_1441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1443_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1444_: u8 = 0; let mut v_isSharedCheck_1455_: u8 = 0; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1455_ = (!lean_is_exclusive(v___x_1440_)) as u8;
if v_isSharedCheck_1455_ == 0 {
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1455_;
state = 1; continue;
} else {
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1455_;
state = 1; continue;
}
} else {
let mut v_a_1456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1458_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1459_: u8 = 0; let mut v_isSharedCheck_1463_: u8 = 0; 
lean_dec(v_a_1428_);
v_a_1456_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1463_ = (!lean_is_exclusive(v___x_1440_)) as u8;
if v_isSharedCheck_1463_ == 0 {
v___x_1458_ = v___x_1440_;
v_isShared_1459_ = v_isSharedCheck_1463_;
state = 3; continue;
} else {
lean_inc(v_a_1456_);
lean_dec(v___x_1440_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
state = 3; continue;
}
}
} else {
let mut v___x_1464_: *mut lean_object = core::ptr::null_mut(); 
v___x_1464_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1464_, 0, v_a_1428_);
return v___x_1464_;
}
}
1 => {
v_snd_1445_ = lean_ctor_get(v_a_1441_, 1);
lean_inc(v_snd_1445_);
lean_dec(v_a_1441_);
v___x_1446_ = lean_array_get_size(v_snd_1445_);
lean_dec(v_snd_1445_);
v___x_1447_ = lean_nat_dec_eq(v___x_1446_, v_size_1426_);
if v___x_1447_ == 0 {
let mut v___x_1448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1451_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_1428_);
v___x_1448_ = lean_mk_string_unchecked(b""Fail"\0".as_ptr().cast(), 4, 4);
v___x_1449_ = lean_alloc_ctor(18, 1, (0) as u32);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
if v_isShared_1444_ == 0 {
lean_ctor_set_tag(v___x_1443_, 1);
lean_ctor_set(v___x_1443_, 0, v___x_1449_);
v___x_1451_ = v___x_1443_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1452_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
state = 2; continue;
}
} else {
let mut v___x_1453_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_1443_);
v___x_1453_ = lean_nat_sub(v_a_1428_, v_size_1426_);
lean_dec(v_a_1428_);
v_a_1428_ = v___x_1453_;
state = 0; continue;
}
}
3 => {
if v_isShared_1459_ == 0 {
v___x_1461_ = v___x_1458_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1462_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyShared_spec__1___redArg___boxed(mut v_size_1465_: *mut lean_object, mut v_seed_1466_: *mut lean_object, mut v_a_1467_: *mut lean_object, mut v___y_1468_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1469_: u64 = 0; let mut v_res_1470_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1469_ = lean_unbox_uint64(v_seed_1466_);
lean_dec_ref(v_seed_1466_);
v_res_1470_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyShared_spec__1___redArg(v_size_1465_, v_seed_boxed_1469_, v_a_1467_);
lean_dec(v_size_1465_);
return v_res_1470_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmptyShared___lam__0(mut v_size_1471_: *mut lean_object, mut v_seed_1472_: u64, mut v_todo_1473_: *mut lean_object) -> *mut lean_object{
let mut v___x_1475_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1477_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1478_: u8 = 0; let mut v___x_1479_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1481_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1482_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1483_: u8 = 0; let mut v_unused_1484_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1485_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1487_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1488_: u8 = 0; let mut v___x_1490_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1491_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1492_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1475_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyShared_spec__1___redArg(v_size_1471_, v_seed_1472_, v_todo_1473_);
if lean_obj_tag(v___x_1475_) == 0 {
let mut v___x_1477_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1478_: u8 = 0; let mut v_isSharedCheck_1483_: u8 = 0; 
v_isSharedCheck_1483_ = (!lean_is_exclusive(v___x_1475_)) as u8;
if v_isSharedCheck_1483_ == 0 {
let mut v_unused_1484_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1484_ = lean_ctor_get(v___x_1475_, 0);
lean_dec(v_unused_1484_);
v___x_1477_ = v___x_1475_;
v_isShared_1478_ = v_isSharedCheck_1483_;
state = 1; continue;
} else {
lean_dec(v___x_1475_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1483_;
state = 1; continue;
}
} else {
let mut v_a_1485_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1487_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1488_: u8 = 0; let mut v_isSharedCheck_1492_: u8 = 0; 
v_a_1485_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1492_ = (!lean_is_exclusive(v___x_1475_)) as u8;
if v_isSharedCheck_1492_ == 0 {
v___x_1487_ = v___x_1475_;
v_isShared_1488_ = v_isSharedCheck_1492_;
state = 3; continue;
} else {
lean_inc(v_a_1485_);
lean_dec(v___x_1475_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
state = 3; continue;
}
}
}
1 => {
v___x_1479_ = lean_box(0);
if v_isShared_1478_ == 0 {
lean_ctor_set(v___x_1477_, 0, v___x_1479_);
v___x_1481_ = v___x_1477_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1482_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
state = 2; continue;
}
}
3 => {
if v_isShared_1488_ == 0 {
v___x_1490_ = v___x_1487_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1491_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmptyShared___lam__0___boxed(mut v_size_1493_: *mut lean_object, mut v_seed_1494_: *mut lean_object, mut v_todo_1495_: *mut lean_object, mut v___y_1496_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1497_: u64 = 0; let mut v_res_1498_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1497_ = lean_unbox_uint64(v_seed_1494_);
lean_dec_ref(v_seed_1494_);
v_res_1498_ = l_benchInsertMissEmptyShared___lam__0(v_size_1493_, v_seed_boxed_1497_, v_todo_1495_);
lean_dec(v_size_1493_);
return v_res_1498_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmptyShared(mut v_seed_1499_: u64, mut v_size_1500_: *mut lean_object) -> *mut lean_object{
let mut v___x_1502_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1504_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1506_: *mut lean_object = core::ptr::null_mut(); 
v___x_1502_ = lean_unsigned_to_nat(100);
v_todo_1503_ = lean_nat_mul(v_size_1500_, v___x_1502_);
v___x_1504_ = lean_box_uint64(v_seed_1499_);
lean_inc(v_todo_1503_);
v___f_1505_ = lean_alloc_closure(l_benchInsertMissEmptyShared___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_1505_, 0, v_size_1500_);
lean_closure_set(v___f_1505_, 1, v___x_1504_);
lean_closure_set(v___f_1505_, 2, v_todo_1503_);
v___x_1506_ = l_timeNanos(v_todo_1503_, v___f_1505_);
return v___x_1506_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchInsertMissEmptyShared___boxed(mut v_seed_1507_: *mut lean_object, mut v_size_1508_: *mut lean_object, mut v_a_1509_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1510_: u64 = 0; let mut v_res_1511_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1510_ = lean_unbox_uint64(v_seed_1507_);
lean_dec_ref(v_seed_1507_);
v_res_1511_ = l_benchInsertMissEmptyShared(v_seed_boxed_1510_, v_size_1508_);
return v_res_1511_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmptyShared_spec__0(mut v_inst_1512_: *mut lean_object, mut v_R_1513_: *mut lean_object, mut v_a_1514_: *mut lean_object, mut v_b_1515_: *mut lean_object, mut v_c_1516_: *mut lean_object) -> *mut lean_object{
let mut v___x_1518_: *mut lean_object = core::ptr::null_mut(); 
v___x_1518_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmptyShared_spec__0___redArg(v_a_1514_, v_b_1515_);
return v___x_1518_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmptyShared_spec__0___boxed(mut v_inst_1519_: *mut lean_object, mut v_R_1520_: *mut lean_object, mut v_a_1521_: *mut lean_object, mut v_b_1522_: *mut lean_object, mut v_c_1523_: *mut lean_object, mut v___y_1524_: *mut lean_object) -> *mut lean_object{
let mut v_res_1525_: *mut lean_object = core::ptr::null_mut(); 
v_res_1525_ = l_WellFounded_opaqueFix_u2083___at___00benchInsertMissEmptyShared_spec__0(v_inst_1519_, v_R_1520_, v_a_1521_, v_b_1522_, v_c_1523_);
return v_res_1525_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyShared_spec__1(mut v_size_1526_: *mut lean_object, mut v_seed_1527_: u64, mut v_inst_1528_: *mut lean_object, mut v_a_1529_: *mut lean_object) -> *mut lean_object{
let mut v___x_1531_: *mut lean_object = core::ptr::null_mut(); 
v___x_1531_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyShared_spec__1___redArg(v_size_1526_, v_seed_1527_, v_a_1529_);
return v___x_1531_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyShared_spec__1___boxed(mut v_size_1532_: *mut lean_object, mut v_seed_1533_: *mut lean_object, mut v_inst_1534_: *mut lean_object, mut v_a_1535_: *mut lean_object, mut v___y_1536_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1537_: u64 = 0; let mut v_res_1538_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1537_ = lean_unbox_uint64(v_seed_1533_);
lean_dec_ref(v_seed_1533_);
v_res_1538_ = l___private_Init_While_0__whileM_erased___at___00benchInsertMissEmptyShared_spec__1(v_size_1532_, v_seed_boxed_1537_, v_inst_1534_, v_a_1535_);
lean_dec(v_size_1532_);
return v_res_1538_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0_spec__1_spec__4(mut v_xs_1539_: *mut lean_object, mut v_v_1540_: u64, mut v_i_1541_: *mut lean_object) -> *mut lean_object{
let mut v___x_1542_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1543_: u8 = 0; let mut v___x_1544_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1545_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1546_: u64 = 0; let mut v___x_1547_: u8 = 0; let mut v___x_1548_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1549_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1551_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1542_ = lean_array_get_size(v_xs_1539_);
v___x_1543_ = lean_nat_dec_lt(v_i_1541_, v___x_1542_);
if v___x_1543_ == 0 {
let mut v___x_1544_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_i_1541_);
v___x_1544_ = lean_box(0);
return v___x_1544_;
} else {
let mut v___x_1545_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1546_: u64 = 0; let mut v___x_1547_: u8 = 0; 
v___x_1545_ = lean_array_fget_borrowed(v_xs_1539_, v_i_1541_);
v___x_1546_ = lean_unbox_uint64(v___x_1545_);
v___x_1547_ = lean_uint64_dec_eq(v___x_1546_, v_v_1540_);
if v___x_1547_ == 0 {
let mut v___x_1548_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1549_: *mut lean_object = core::ptr::null_mut(); 
v___x_1548_ = lean_unsigned_to_nat(1);
v___x_1549_ = lean_nat_add(v_i_1541_, v___x_1548_);
lean_dec(v_i_1541_);
v_i_1541_ = v___x_1549_;
state = 0; continue;
} else {
let mut v___x_1551_: *mut lean_object = core::ptr::null_mut(); 
v___x_1551_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_1551_, 0, v_i_1541_);
return v___x_1551_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0_spec__1_spec__4___boxed(mut v_xs_1552_: *mut lean_object, mut v_v_1553_: *mut lean_object, mut v_i_1554_: *mut lean_object) -> *mut lean_object{
let mut v_v_boxed_1555_: u64 = 0; let mut v_res_1556_: *mut lean_object = core::ptr::null_mut(); 
v_v_boxed_1555_ = lean_unbox_uint64(v_v_1553_);
lean_dec_ref(v_v_1553_);
v_res_1556_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0_spec__1_spec__4(v_xs_1552_, v_v_boxed_1555_, v_i_1554_);
lean_dec_ref(v_xs_1552_);
return v_res_1556_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0_spec__1(mut v_xs_1557_: *mut lean_object, mut v_v_1558_: u64) -> *mut lean_object{
let mut v___x_1559_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1560_: *mut lean_object = core::ptr::null_mut(); 
v___x_1559_ = lean_unsigned_to_nat(0);
v___x_1560_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0_spec__1_spec__4(v_xs_1557_, v_v_1558_, v___x_1559_);
return v___x_1560_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0_spec__1___boxed(mut v_xs_1561_: *mut lean_object, mut v_v_1562_: *mut lean_object) -> *mut lean_object{
let mut v_v_boxed_1563_: u64 = 0; let mut v_res_1564_: *mut lean_object = core::ptr::null_mut(); 
v_v_boxed_1563_ = lean_unbox_uint64(v_v_1562_);
lean_dec_ref(v_v_1562_);
v_res_1564_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0_spec__1(v_xs_1561_, v_v_boxed_1563_);
lean_dec_ref(v_xs_1561_);
return v_res_1564_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(mut v_x_1565_: *mut lean_object, mut v_x_1566_: usize, mut v_x_1567_: u64) -> *mut lean_object{
let mut v_es_1568_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1570_: usize = 0; let mut v___x_1571_: usize = 0; let mut v___x_1572_: usize = 0; let mut v___x_1573_: usize = 0; let mut v___x_1574_: usize = 0; let mut v_j_1575_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_1576_: *mut lean_object = core::ptr::null_mut(); let mut v_key_1577_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1578_: u64 = 0; let mut v___x_1579_: u8 = 0; let mut v___x_1581_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1582_: u8 = 0; let mut v___x_1583_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1585_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1586_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1587_: u8 = 0; let mut v_unused_1588_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1590_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1591_: u8 = 0; let mut v_node_1592_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1594_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1595_: u8 = 0; let mut v_entries_1596_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1597_: usize = 0; let mut v_newNode_1598_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1599_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1601_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1602_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1604_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1605_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1606_: *mut lean_object = core::ptr::null_mut(); let mut v_val_1607_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1608_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1611_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1612_: u8 = 0; let mut v___x_1614_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1615_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1617_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1618_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1619_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1620_: u8 = 0; let mut v_isSharedCheck_1621_: u8 = 0; let mut v_isSharedCheck_1622_: u8 = 0; let mut v_unused_1623_: *mut lean_object = core::ptr::null_mut(); let mut v_ks_1624_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_1625_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1627_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1628_: u8 = 0; let mut v___x_1629_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1631_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1632_: *mut lean_object = core::ptr::null_mut(); let mut v_val_1633_: *mut lean_object = core::ptr::null_mut(); let mut v_keys_x27_1634_: *mut lean_object = core::ptr::null_mut(); let mut v_vals_x27_1635_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1637_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1638_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1639_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_1565_) == 0 {
let mut v_es_1568_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1570_: usize = 0; let mut v___x_1571_: usize = 0; let mut v___x_1572_: usize = 0; let mut v___x_1573_: usize = 0; let mut v___x_1574_: usize = 0; let mut v_j_1575_: *mut lean_object = core::ptr::null_mut(); let mut v_entry_1576_: *mut lean_object = core::ptr::null_mut(); 
v_es_1568_ = lean_ctor_get(v_x_1565_, 0);
v___x_1569_ = lean_box(2);
v___x_1570_ = 5usize;
v___x_1571_ = 1usize;
v___x_1572_ = lean_usize_shift_left(v___x_1571_, v___x_1570_);
v___x_1573_ = lean_usize_sub(v___x_1572_, v___x_1571_);
v___x_1574_ = lean_usize_land(v_x_1566_, v___x_1573_);
v_j_1575_ = lean_usize_to_nat(v___x_1574_);
v_entry_1576_ = lean_array_get(v___x_1569_, v_es_1568_, v_j_1575_);
match lean_obj_tag(v_entry_1576_)
{
0 => {
let mut v_key_1577_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1578_: u64 = 0; let mut v___x_1579_: u8 = 0; 
v_key_1577_ = lean_ctor_get(v_entry_1576_, 0);
lean_inc(v_key_1577_);
lean_dec_ref_known(v_entry_1576_, 2);
v___x_1578_ = lean_unbox_uint64(v_key_1577_);
lean_dec(v_key_1577_);
v___x_1579_ = lean_uint64_dec_eq(v_x_1567_, v___x_1578_);
if v___x_1579_ == 0 {
lean_dec(v_j_1575_);
return v_x_1565_;
} else {
let mut v___x_1581_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1582_: u8 = 0; let mut v_isSharedCheck_1587_: u8 = 0; 
lean_inc_ref(v_es_1568_);
v_isSharedCheck_1587_ = (!lean_is_exclusive(v_x_1565_)) as u8;
if v_isSharedCheck_1587_ == 0 {
let mut v_unused_1588_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1588_ = lean_ctor_get(v_x_1565_, 0);
lean_dec(v_unused_1588_);
v___x_1581_ = v_x_1565_;
v_isShared_1582_ = v_isSharedCheck_1587_;
state = 1; continue;
} else {
lean_dec(v_x_1565_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1587_;
state = 1; continue;
}
}
}
1 => {
let mut v___x_1590_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1591_: u8 = 0; let mut v_isSharedCheck_1622_: u8 = 0; 
lean_inc_ref(v_es_1568_);
v_isSharedCheck_1622_ = (!lean_is_exclusive(v_x_1565_)) as u8;
if v_isSharedCheck_1622_ == 0 {
let mut v_unused_1623_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1623_ = lean_ctor_get(v_x_1565_, 0);
lean_dec(v_unused_1623_);
v___x_1590_ = v_x_1565_;
v_isShared_1591_ = v_isSharedCheck_1622_;
state = 3; continue;
} else {
lean_dec(v_x_1565_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1622_;
state = 3; continue;
}
}
_ => {
lean_dec(v_j_1575_);
return v_x_1565_;
}
}
} else {
let mut v_ks_1624_: *mut lean_object = core::ptr::null_mut(); let mut v_vs_1625_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1627_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1628_: u8 = 0; let mut v_isSharedCheck_1639_: u8 = 0; 
v_ks_1624_ = lean_ctor_get(v_x_1565_, 0);
v_vs_1625_ = lean_ctor_get(v_x_1565_, 1);
v_isSharedCheck_1639_ = (!lean_is_exclusive(v_x_1565_)) as u8;
if v_isSharedCheck_1639_ == 0 {
v___x_1627_ = v_x_1565_;
v_isShared_1628_ = v_isSharedCheck_1639_;
state = 10; continue;
} else {
lean_inc(v_vs_1625_);
lean_inc(v_ks_1624_);
lean_dec(v_x_1565_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1639_;
state = 10; continue;
}
}
}
1 => {
v___x_1583_ = lean_array_set(v_es_1568_, v_j_1575_, v___x_1569_);
lean_dec(v_j_1575_);
if v_isShared_1582_ == 0 {
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1586_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
state = 2; continue;
}
}
3 => {
v_node_1592_ = lean_ctor_get(v_entry_1576_, 0);
v_isSharedCheck_1621_ = (!lean_is_exclusive(v_entry_1576_)) as u8;
if v_isSharedCheck_1621_ == 0 {
v___x_1594_ = v_entry_1576_;
v_isShared_1595_ = v_isSharedCheck_1621_;
state = 4; continue;
} else {
lean_inc(v_node_1592_);
lean_dec(v_entry_1576_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1621_;
state = 4; continue;
}
}
10 => {
v___x_1629_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0_spec__1(v_ks_1624_, v_x_1567_);
if lean_obj_tag(v___x_1629_) == 0 {
let mut v___x_1631_: *mut lean_object = core::ptr::null_mut(); 
if v_isShared_1628_ == 0 {
v___x_1631_ = v___x_1627_;
state = 11; continue;
} else {
let mut v_reuseFailAlloc_1632_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_ks_1624_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_vs_1625_);
v___x_1631_ = v_reuseFailAlloc_1632_;
state = 11; continue;
}
} else {
let mut v_val_1633_: *mut lean_object = core::ptr::null_mut(); let mut v_keys_x27_1634_: *mut lean_object = core::ptr::null_mut(); let mut v_vals_x27_1635_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1637_: *mut lean_object = core::ptr::null_mut(); 
v_val_1633_ = lean_ctor_get(v___x_1629_, 0);
lean_inc_n(v_val_1633_, 2);
lean_dec_ref_known(v___x_1629_, 1);
v_keys_x27_1634_ = l_Array_eraseIdx___redArg(v_ks_1624_, v_val_1633_);
v_vals_x27_1635_ = l_Array_eraseIdx___redArg(v_vs_1625_, v_val_1633_);
if v_isShared_1628_ == 0 {
lean_ctor_set(v___x_1627_, 1, v_vals_x27_1635_);
lean_ctor_set(v___x_1627_, 0, v_keys_x27_1634_);
v___x_1637_ = v___x_1627_;
state = 12; continue;
} else {
let mut v_reuseFailAlloc_1638_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_keys_x27_1634_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_vals_x27_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
state = 12; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0___redArg___boxed(mut v_x_1640_: *mut lean_object, mut v_x_1641_: *mut lean_object, mut v_x_1642_: *mut lean_object) -> *mut lean_object{
let mut v_x_3904__boxed_1643_: usize = 0; let mut v_x_3905__boxed_1644_: u64 = 0; let mut v_res_1645_: *mut lean_object = core::ptr::null_mut(); 
v_x_3904__boxed_1643_ = lean_unbox_usize(v_x_1641_);
lean_dec(v_x_1641_);
v_x_3905__boxed_1644_ = lean_unbox_uint64(v_x_1642_);
lean_dec_ref(v_x_1642_);
v_res_1645_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(v_x_1640_, v_x_3904__boxed_1643_, v_x_3905__boxed_1644_);
return v_res_1645_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0___redArg(mut v_x_1646_: *mut lean_object, mut v_x_1647_: u64) -> *mut lean_object{
let mut v_h_1648_: usize = 0; let mut v___x_1649_: *mut lean_object = core::ptr::null_mut(); 
v_h_1648_ = lean_uint64_to_usize(v_x_1647_);
v___x_1649_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(v_x_1646_, v_h_1648_, v_x_1647_);
return v___x_1649_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0___redArg___boxed(mut v_x_1650_: *mut lean_object, mut v_x_1651_: *mut lean_object) -> *mut lean_object{
let mut v_x_4046__boxed_1652_: u64 = 0; let mut v_res_1653_: *mut lean_object = core::ptr::null_mut(); 
v_x_4046__boxed_1652_ = lean_unbox_uint64(v_x_1651_);
lean_dec_ref(v_x_1651_);
v_res_1653_ = l_Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0___redArg(v_x_1650_, v_x_4046__boxed_1652_);
return v_res_1653_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(mut v_a_1654_: *mut lean_object, mut v_b_1655_: *mut lean_object) -> *mut lean_object{
let mut v_countdown_1657_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_1658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1660_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1661_: u8 = 0; let mut v_it_1663_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1665_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1667_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1668_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1669_: u8 = 0; let mut v_memoizedLeft_1670_: *mut lean_object = core::ptr::null_mut(); let mut v_left_1671_: *mut lean_object = core::ptr::null_mut(); let mut v_right_1672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1674_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1675_: u8 = 0; let mut v___x_1676_: u64 = 0; let mut v___x_1677_: u64 = 0; let mut v___x_1678_: u64 = 0; let mut v___x_1679_: u64 = 0; let mut v___x_1680_: u64 = 0; let mut v___x_1681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1682_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1684_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1685_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1686_: u8 = 0; let mut v_unused_1687_: *mut lean_object = core::ptr::null_mut(); let mut v_right_1688_: *mut lean_object = core::ptr::null_mut(); let mut v_left_1689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1692_: u8 = 0; let mut v_val_1693_: *mut lean_object = core::ptr::null_mut(); let mut v_remaining_1694_: *mut lean_object = core::ptr::null_mut(); let mut v_inner_1695_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1697_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1698_: u8 = 0; let mut v___x_1699_: u64 = 0; let mut v___x_1700_: u64 = 0; let mut v___x_1701_: u64 = 0; let mut v___x_1702_: u64 = 0; let mut v___x_1703_: u64 = 0; let mut v_zero_1704_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_1705_: u8 = 0; let mut v___x_1707_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1708_: u8 = 0; let mut v___x_1709_: u64 = 0; let mut v___x_1710_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1711_: u64 = 0; let mut v___x_1712_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1713_: u8 = 0; let mut v___x_1714_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1716_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1717_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1719_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1720_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1721_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1723_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1725_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1727_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1728_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1729_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1730_: u8 = 0; let mut v_unused_1731_: *mut lean_object = core::ptr::null_mut(); let mut v_n_1732_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1733_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1735_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1737_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1738_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1739_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1740_: u8 = 0; let mut v_isSharedCheck_1741_: u8 = 0; let mut v_unused_1742_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1743_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1744_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_countdown_1657_ = lean_ctor_get(v_a_1654_, 0);
v_inner_1658_ = lean_ctor_get(v_a_1654_, 1);
v_isSharedCheck_1744_ = (!lean_is_exclusive(v_a_1654_)) as u8;
if v_isSharedCheck_1744_ == 0 {
v___x_1660_ = v_a_1654_;
v_isShared_1661_ = v_isSharedCheck_1744_;
state = 1; continue;
} else {
lean_inc(v_inner_1658_);
lean_inc(v_countdown_1657_);
lean_dec(v_a_1654_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1744_;
state = 1; continue;
}
}
1 => {
v___x_1668_ = lean_unsigned_to_nat(1);
v___x_1669_ = lean_nat_dec_eq(v_countdown_1657_, v___x_1668_);
if v___x_1669_ == 0 {
let mut v_memoizedLeft_1670_: *mut lean_object = core::ptr::null_mut(); 
v_memoizedLeft_1670_ = lean_ctor_get(v_inner_1658_, 1);
lean_inc(v_memoizedLeft_1670_);
if lean_obj_tag(v_memoizedLeft_1670_) == 0 {
let mut v_left_1671_: *mut lean_object = core::ptr::null_mut(); let mut v_right_1672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1674_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1675_: u8 = 0; let mut v_isSharedCheck_1686_: u8 = 0; 
v_left_1671_ = lean_ctor_get(v_inner_1658_, 0);
v_right_1672_ = lean_ctor_get(v_inner_1658_, 2);
v_isSharedCheck_1686_ = (!lean_is_exclusive(v_inner_1658_)) as u8;
if v_isSharedCheck_1686_ == 0 {
let mut v_unused_1687_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1687_ = lean_ctor_get(v_inner_1658_, 1);
lean_dec(v_unused_1687_);
v___x_1674_ = v_inner_1658_;
v_isShared_1675_ = v_isSharedCheck_1686_;
state = 4; continue;
} else {
lean_inc(v_right_1672_);
lean_inc(v_left_1671_);
lean_dec(v_inner_1658_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1686_;
state = 4; continue;
}
} else {
let mut v_right_1688_: *mut lean_object = core::ptr::null_mut(); let mut v_left_1689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1692_: u8 = 0; let mut v_isSharedCheck_1741_: u8 = 0; 
v_right_1688_ = lean_ctor_get(v_inner_1658_, 2);
v_left_1689_ = lean_ctor_get(v_inner_1658_, 0);
v_isSharedCheck_1741_ = (!lean_is_exclusive(v_inner_1658_)) as u8;
if v_isSharedCheck_1741_ == 0 {
let mut v_unused_1742_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1742_ = lean_ctor_get(v_inner_1658_, 1);
lean_dec(v_unused_1742_);
v___x_1691_ = v_inner_1658_;
v_isShared_1692_ = v_isSharedCheck_1741_;
state = 6; continue;
} else {
lean_inc(v_right_1688_);
lean_inc(v_left_1689_);
lean_dec(v_inner_1658_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1741_;
state = 6; continue;
}
}
} else {
let mut v___x_1743_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_1660_);
lean_dec(v_inner_1658_);
lean_dec(v_countdown_1657_);
v___x_1743_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1743_, 0, v_b_1655_);
return v___x_1743_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg___boxed(mut v_a_1745_: *mut lean_object, mut v_b_1746_: *mut lean_object, mut v___y_1747_: *mut lean_object) -> *mut lean_object{
let mut v_res_1748_: *mut lean_object = core::ptr::null_mut(); 
v_res_1748_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(v_a_1745_, v_b_1746_);
return v_res_1748_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg(mut v_eraseIter_1749_: u64, mut v_newIter_1750_: *mut lean_object, mut v_size_1751_: *mut lean_object, mut v_a_1752_: *mut lean_object) -> *mut lean_object{
let mut v_fst_1754_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1755_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1757_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1758_: u8 = 0; let mut v___x_1759_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1760_: u8 = 0; let mut v___x_1761_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1762_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1763_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1764_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1766_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1767_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1768_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1769_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1771_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1773_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1776_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1777_: u8 = 0; let mut v___x_1779_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1780_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1781_: u8 = 0; let mut v___x_1783_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1784_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1785_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1786_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_1754_ = lean_ctor_get(v_a_1752_, 0);
v_snd_1755_ = lean_ctor_get(v_a_1752_, 1);
v_isSharedCheck_1786_ = (!lean_is_exclusive(v_a_1752_)) as u8;
if v_isSharedCheck_1786_ == 0 {
v___x_1757_ = v_a_1752_;
v_isShared_1758_ = v_isSharedCheck_1786_;
state = 1; continue;
} else {
lean_inc(v_snd_1755_);
lean_inc(v_fst_1754_);
lean_dec(v_a_1752_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1786_;
state = 1; continue;
}
}
1 => {
v___x_1759_ = lean_unsigned_to_nat(0);
v___x_1760_ = lean_nat_dec_eq(v_snd_1755_, v___x_1759_);
if v___x_1760_ == 0 {
let mut v___x_1761_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1762_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1763_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1764_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1766_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1767_: *mut lean_object = core::ptr::null_mut(); 
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_box_uint64(v_eraseIter_1749_);
lean_inc_ref(v_newIter_1750_);
v___x_1763_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1761_);
lean_ctor_set(v___x_1763_, 2, v_newIter_1750_);
v___x_1764_ = lean_unsigned_to_nat(1);
v___x_1765_ = lean_nat_add(v_size_1751_, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v___x_1763_);
v___x_1767_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(v___x_1766_, v_fst_1754_);
if lean_obj_tag(v___x_1767_) == 0 {
let mut v_a_1768_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1769_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1771_: *mut lean_object = core::ptr::null_mut(); 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1769_ = lean_nat_sub(v_snd_1755_, v_size_1751_);
lean_dec(v_snd_1755_);
if v_isShared_1758_ == 0 {
lean_ctor_set(v___x_1757_, 1, v___x_1769_);
lean_ctor_set(v___x_1757_, 0, v_a_1768_);
v___x_1771_ = v___x_1757_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1773_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1768_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1773_;
state = 2; continue;
}
} else {
let mut v_a_1774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1776_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1777_: u8 = 0; let mut v_isSharedCheck_1781_: u8 = 0; 
lean_del_object(v___x_1757_);
lean_dec(v_snd_1755_);
lean_dec_ref(v_newIter_1750_);
v_a_1774_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1781_ = (!lean_is_exclusive(v___x_1767_)) as u8;
if v_isSharedCheck_1781_ == 0 {
v___x_1776_ = v___x_1767_;
v_isShared_1777_ = v_isSharedCheck_1781_;
state = 3; continue;
} else {
lean_inc(v_a_1774_);
lean_dec(v___x_1767_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
state = 3; continue;
}
}
} else {
let mut v___x_1783_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_newIter_1750_);
if v_isShared_1758_ == 0 {
v___x_1783_ = v___x_1757_;
state = 5; continue;
} else {
let mut v_reuseFailAlloc_1785_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fst_1754_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_snd_1755_);
v___x_1783_ = v_reuseFailAlloc_1785_;
state = 5; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg___boxed(mut v_eraseIter_1787_: *mut lean_object, mut v_newIter_1788_: *mut lean_object, mut v_size_1789_: *mut lean_object, mut v_a_1790_: *mut lean_object, mut v___y_1791_: *mut lean_object) -> *mut lean_object{
let mut v_eraseIter_boxed_1792_: u64 = 0; let mut v_res_1793_: *mut lean_object = core::ptr::null_mut(); 
v_eraseIter_boxed_1792_ = lean_unbox_uint64(v_eraseIter_1787_);
lean_dec_ref(v_eraseIter_1787_);
v_res_1793_ = l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg(v_eraseIter_boxed_1792_, v_newIter_1788_, v_size_1789_, v_a_1790_);
lean_dec(v_size_1789_);
return v_res_1793_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchEraseInsert___lam__0(mut v_seed_1794_: u64, mut v_newIter_1795_: *mut lean_object, mut v_size_1796_: *mut lean_object, mut v___x_1797_: *mut lean_object) -> *mut lean_object{
let mut v___x_1799_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1801_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1802_: u8 = 0; let mut v___x_1803_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1805_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1806_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1807_: u8 = 0; let mut v_unused_1808_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1809_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1811_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1812_: u8 = 0; let mut v___x_1814_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1815_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1816_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1799_ = l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg(v_seed_1794_, v_newIter_1795_, v_size_1796_, v___x_1797_);
if lean_obj_tag(v___x_1799_) == 0 {
let mut v___x_1801_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1802_: u8 = 0; let mut v_isSharedCheck_1807_: u8 = 0; 
v_isSharedCheck_1807_ = (!lean_is_exclusive(v___x_1799_)) as u8;
if v_isSharedCheck_1807_ == 0 {
let mut v_unused_1808_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1808_ = lean_ctor_get(v___x_1799_, 0);
lean_dec(v_unused_1808_);
v___x_1801_ = v___x_1799_;
v_isShared_1802_ = v_isSharedCheck_1807_;
state = 1; continue;
} else {
lean_dec(v___x_1799_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1807_;
state = 1; continue;
}
} else {
let mut v_a_1809_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1811_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1812_: u8 = 0; let mut v_isSharedCheck_1816_: u8 = 0; 
v_a_1809_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1816_ = (!lean_is_exclusive(v___x_1799_)) as u8;
if v_isSharedCheck_1816_ == 0 {
v___x_1811_ = v___x_1799_;
v_isShared_1812_ = v_isSharedCheck_1816_;
state = 3; continue;
} else {
lean_inc(v_a_1809_);
lean_dec(v___x_1799_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
state = 3; continue;
}
}
}
1 => {
v___x_1803_ = lean_box(0);
if v_isShared_1802_ == 0 {
lean_ctor_set(v___x_1801_, 0, v___x_1803_);
v___x_1805_ = v___x_1801_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1806_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
state = 2; continue;
}
}
3 => {
if v_isShared_1812_ == 0 {
v___x_1814_ = v___x_1811_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1815_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_benchEraseInsert___lam__0___boxed(mut v_seed_1817_: *mut lean_object, mut v_newIter_1818_: *mut lean_object, mut v_size_1819_: *mut lean_object, mut v___x_1820_: *mut lean_object, mut v___y_1821_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1822_: u64 = 0; let mut v_res_1823_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1822_ = lean_unbox_uint64(v_seed_1817_);
lean_dec_ref(v_seed_1817_);
v_res_1823_ = l_benchEraseInsert___lam__0(v_seed_boxed_1822_, v_newIter_1818_, v_size_1819_, v___x_1820_);
lean_dec(v_size_1819_);
return v_res_1823_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchEraseInsert(mut v_seed_1824_: u64, mut v_size_1825_: *mut lean_object) -> *mut lean_object{
let mut v_map_1827_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1828_: *mut lean_object = core::ptr::null_mut(); let mut v_todo_1829_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1830_: *mut lean_object = core::ptr::null_mut(); let mut v_newIter_1831_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1832_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1833_: *mut lean_object = core::ptr::null_mut(); let mut v___f_1834_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1835_: *mut lean_object = core::ptr::null_mut(); 
v_map_1827_ = l_mkMapWithCap(v_seed_1824_, v_size_1825_);
v___x_1828_ = lean_unsigned_to_nat(100);
v_todo_1829_ = lean_nat_mul(v_size_1825_, v___x_1828_);
v___x_1830_ = lean_box_uint64(v_seed_1824_);
lean_inc(v_size_1825_);
v_newIter_1831_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_newIter_1831_, 0, v_size_1825_);
lean_ctor_set(v_newIter_1831_, 1, v___x_1830_);
lean_inc(v_todo_1829_);
v___x_1832_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1832_, 0, v_map_1827_);
lean_ctor_set(v___x_1832_, 1, v_todo_1829_);
v___x_1833_ = lean_box_uint64(v_seed_1824_);
v___f_1834_ = lean_alloc_closure(l_benchEraseInsert___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
lean_closure_set(v___f_1834_, 0, v___x_1833_);
lean_closure_set(v___f_1834_, 1, v_newIter_1831_);
lean_closure_set(v___f_1834_, 2, v_size_1825_);
lean_closure_set(v___f_1834_, 3, v___x_1832_);
v___x_1835_ = l_timeNanos(v_todo_1829_, v___f_1834_);
return v___x_1835_;
}
#[no_mangle] pub unsafe extern "C" fn l_benchEraseInsert___boxed(mut v_seed_1836_: *mut lean_object, mut v_size_1837_: *mut lean_object, mut v_a_1838_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1839_: u64 = 0; let mut v_res_1840_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1839_ = lean_unbox_uint64(v_seed_1836_);
lean_dec_ref(v_seed_1836_);
v_res_1840_ = l_benchEraseInsert(v_seed_boxed_1839_, v_size_1837_);
return v_res_1840_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0(mut v_00_u03b2_1841_: *mut lean_object, mut v_x_1842_: *mut lean_object, mut v_x_1843_: u64) -> *mut lean_object{
let mut v___x_1844_: *mut lean_object = core::ptr::null_mut(); 
v___x_1844_ = l_Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0___redArg(v_x_1842_, v_x_1843_);
return v___x_1844_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0___boxed(mut v_00_u03b2_1845_: *mut lean_object, mut v_x_1846_: *mut lean_object, mut v_x_1847_: *mut lean_object) -> *mut lean_object{
let mut v_x_4334__boxed_1848_: u64 = 0; let mut v_res_1849_: *mut lean_object = core::ptr::null_mut(); 
v_x_4334__boxed_1848_ = lean_unbox_uint64(v_x_1847_);
lean_dec_ref(v_x_1847_);
v_res_1849_ = l_Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0(v_00_u03b2_1845_, v_x_1846_, v_x_4334__boxed_1848_);
return v_res_1849_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1(mut v_inst_1850_: *mut lean_object, mut v_R_1851_: *mut lean_object, mut v_a_1852_: *mut lean_object, mut v_b_1853_: *mut lean_object, mut v_c_1854_: *mut lean_object) -> *mut lean_object{
let mut v___x_1856_: *mut lean_object = core::ptr::null_mut(); 
v___x_1856_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___redArg(v_a_1852_, v_b_1853_);
return v___x_1856_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1___boxed(mut v_inst_1857_: *mut lean_object, mut v_R_1858_: *mut lean_object, mut v_a_1859_: *mut lean_object, mut v_b_1860_: *mut lean_object, mut v_c_1861_: *mut lean_object, mut v___y_1862_: *mut lean_object) -> *mut lean_object{
let mut v_res_1863_: *mut lean_object = core::ptr::null_mut(); 
v_res_1863_ = l_WellFounded_opaqueFix_u2083___at___00benchEraseInsert_spec__1(v_inst_1857_, v_R_1858_, v_a_1859_, v_b_1860_, v_c_1861_);
return v_res_1863_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2(mut v_eraseIter_1864_: u64, mut v_newIter_1865_: *mut lean_object, mut v_size_1866_: *mut lean_object, mut v_inst_1867_: *mut lean_object, mut v_a_1868_: *mut lean_object) -> *mut lean_object{
let mut v___x_1870_: *mut lean_object = core::ptr::null_mut(); 
v___x_1870_ = l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___redArg(v_eraseIter_1864_, v_newIter_1865_, v_size_1866_, v_a_1868_);
return v___x_1870_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2___boxed(mut v_eraseIter_1871_: *mut lean_object, mut v_newIter_1872_: *mut lean_object, mut v_size_1873_: *mut lean_object, mut v_inst_1874_: *mut lean_object, mut v_a_1875_: *mut lean_object, mut v___y_1876_: *mut lean_object) -> *mut lean_object{
let mut v_eraseIter_boxed_1877_: u64 = 0; let mut v_res_1878_: *mut lean_object = core::ptr::null_mut(); 
v_eraseIter_boxed_1877_ = lean_unbox_uint64(v_eraseIter_1871_);
lean_dec_ref(v_eraseIter_1871_);
v_res_1878_ = l___private_Init_While_0__whileM_erased___at___00benchEraseInsert_spec__2(v_eraseIter_boxed_1877_, v_newIter_1872_, v_size_1873_, v_inst_1874_, v_a_1875_);
lean_dec(v_size_1873_);
return v_res_1878_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0(mut v_00_u03b2_1879_: *mut lean_object, mut v_x_1880_: *mut lean_object, mut v_x_1881_: usize, mut v_x_1882_: u64) -> *mut lean_object{
let mut v___x_1883_: *mut lean_object = core::ptr::null_mut(); 
v___x_1883_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0___redArg(v_x_1880_, v_x_1881_, v_x_1882_);
return v___x_1883_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0___boxed(mut v_00_u03b2_1884_: *mut lean_object, mut v_x_1885_: *mut lean_object, mut v_x_1886_: *mut lean_object, mut v_x_1887_: *mut lean_object) -> *mut lean_object{
let mut v_x_4358__boxed_1888_: usize = 0; let mut v_x_4359__boxed_1889_: u64 = 0; let mut v_res_1890_: *mut lean_object = core::ptr::null_mut(); 
v_x_4358__boxed_1888_ = lean_unbox_usize(v_x_1886_);
lean_dec(v_x_1886_);
v_x_4359__boxed_1889_ = lean_unbox_uint64(v_x_1887_);
lean_dec_ref(v_x_1887_);
v_res_1890_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00benchEraseInsert_spec__0_spec__0(v_00_u03b2_1884_, v_x_1885_, v_x_4358__boxed_1888_, v_x_4359__boxed_1889_);
return v_res_1890_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00main_spec__0(mut v_msg_1891_: *mut lean_object) -> *mut lean_object{
let mut v___x_1893_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1894_: *mut lean_object = core::ptr::null_mut(); let mut v___x_711__overap_1895_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1896_: *mut lean_object = core::ptr::null_mut(); 
v___x_1893_ = l_instInhabitedError;
v___x_1894_ = lean_alloc_closure(l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___x_1894_, 0, lean_box(0));
lean_closure_set(v___x_1894_, 1, lean_box(0));
lean_closure_set(v___x_1894_, 2, v___x_1893_);
v___x_711__overap_1895_ = lean_panic_fn_borrowed(v___x_1894_, v_msg_1891_);
lean_dec_ref(v___x_1894_);
v___x_1896_ = lean_apply_1(v___x_711__overap_1895_, lean_box(0));
return v___x_1896_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00main_spec__0___boxed(mut v_msg_1897_: *mut lean_object, mut v___y_1898_: *mut lean_object) -> *mut lean_object{
let mut v_res_1899_: *mut lean_object = core::ptr::null_mut(); 
v_res_1899_ = l_panic___at___00main_spec__0(v_msg_1897_);
return v_res_1899_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(mut v_s_1900_: *mut lean_object) -> *mut lean_object{
let mut v___x_1902_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_1903_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1904_: *mut lean_object = core::ptr::null_mut(); 
v___x_1902_ = lean_get_stdout();
v_putStr_1903_ = lean_ctor_get(v___x_1902_, 4);
lean_inc_ref(v_putStr_1903_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = lean_apply_2(v_putStr_1903_, v_s_1900_, lean_box(0));
return v___x_1904_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__1___boxed(mut v_s_1905_: *mut lean_object, mut v_a_1906_: *mut lean_object) -> *mut lean_object{
let mut v_res_1907_: *mut lean_object = core::ptr::null_mut(); 
v_res_1907_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(v_s_1905_);
return v_res_1907_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_1908_: *mut lean_object) -> *mut lean_object{
let mut v___x_1910_: u32 = 0; let mut v___x_1911_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1912_: *mut lean_object = core::ptr::null_mut(); 
v___x_1910_ = 10;
v___x_1911_ = lean_string_push(v_s_1908_, v___x_1910_);
v___x_1912_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(v___x_1911_);
return v___x_1912_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_1913_: *mut lean_object, mut v_a_1914_: *mut lean_object) -> *mut lean_object{
let mut v_res_1915_: *mut lean_object = core::ptr::null_mut(); 
v_res_1915_ = l_IO_println___at___00main_spec__1(v_s_1913_);
return v_res_1915_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00main_spec__2___redArg(mut v_seed_1916_: u64, mut v_size_1917_: *mut lean_object, mut v_as_x27_1918_: *mut lean_object, mut v_b_1919_: *mut lean_object) -> *mut lean_object{
let mut v___x_1921_: *mut lean_object = core::ptr::null_mut(); let mut v_head_1922_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_1923_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1924_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1925_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1926_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1927_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1928_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1929_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1930_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1931_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1932_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1933_: f64 = 0.0; let mut v___x_1934_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1935_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1936_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1937_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1938_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1939_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1941_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1943_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1944_: u8 = 0; let mut v___x_1946_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1947_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1948_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_as_x27_1918_) == 0 {
let mut v___x_1921_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_size_1917_);
v___x_1921_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_1921_, 0, v_b_1919_);
return v___x_1921_;
} else {
let mut v_head_1922_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_1923_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1924_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1925_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1926_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1927_: *mut lean_object = core::ptr::null_mut(); 
v_head_1922_ = lean_ctor_get(v_as_x27_1918_, 0);
v_tail_1923_ = lean_ctor_get(v_as_x27_1918_, 1);
v_fst_1924_ = lean_ctor_get(v_head_1922_, 0);
v_snd_1925_ = lean_ctor_get(v_head_1922_, 1);
v___x_1926_ = lean_box_uint64(v_seed_1916_);
lean_inc(v_snd_1925_);
lean_inc(v_size_1917_);
v___x_1927_ = lean_apply_3(v_snd_1925_, v___x_1926_, v_size_1917_, lean_box(0));
if lean_obj_tag(v___x_1927_) == 0 {
let mut v_a_1928_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1929_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1930_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1931_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1932_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1933_: f64 = 0.0; let mut v___x_1934_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1935_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1936_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1937_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1938_: *mut lean_object = core::ptr::null_mut(); 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = lean_mk_string_unchecked(b""measurement: "\0".as_ptr().cast(), 13, 13);
v___x_1930_ = lean_string_append(v___x_1929_, v_fst_1924_);
v___x_1931_ = lean_mk_string_unchecked(b"" "\0".as_ptr().cast(), 1, 1);
v___x_1932_ = lean_string_append(v___x_1930_, v___x_1931_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = lean_unbox_float(v_a_1928_);
lean_dec(v_a_1928_);
v___x_1934_ = lean_float_to_string(v___x_1933_);
v___x_1935_ = lean_string_append(v___x_1932_, v___x_1934_);
lean_dec_ref(v___x_1934_);
v___x_1936_ = lean_mk_string_unchecked(b"" s"\0".as_ptr().cast(), 2, 2);
v___x_1937_ = lean_string_append(v___x_1935_, v___x_1936_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = l_IO_println___at___00main_spec__1(v___x_1937_);
if lean_obj_tag(v___x_1938_) == 0 {
let mut v___x_1939_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_1938_, 1);
v___x_1939_ = lean_box(0);
v_as_x27_1918_ = v_tail_1923_;
v_b_1919_ = v___x_1939_;
state = 0; continue;
} else {
lean_dec(v_size_1917_);
return v___x_1938_;
}
} else {
let mut v_a_1941_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1943_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1944_: u8 = 0; let mut v_isSharedCheck_1948_: u8 = 0; 
lean_dec(v_size_1917_);
v_a_1941_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1948_ = (!lean_is_exclusive(v___x_1927_)) as u8;
if v_isSharedCheck_1948_ == 0 {
v___x_1943_ = v___x_1927_;
v_isShared_1944_ = v_isSharedCheck_1948_;
state = 1; continue;
} else {
lean_inc(v_a_1941_);
lean_dec(v___x_1927_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
state = 1; continue;
}
}
}
}
1 => {
if v_isShared_1944_ == 0 {
v___x_1946_ = v___x_1943_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1947_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(mut v_seed_1949_: *mut lean_object, mut v_size_1950_: *mut lean_object, mut v_as_x27_1951_: *mut lean_object, mut v_b_1952_: *mut lean_object, mut v___y_1953_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_1954_: u64 = 0; let mut v_res_1955_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_1954_ = lean_unbox_uint64(v_seed_1949_);
lean_dec_ref(v_seed_1949_);
v_res_1955_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_seed_boxed_1954_, v_size_1950_, v_as_x27_1951_, v_b_1952_);
lean_dec(v_as_x27_1951_);
return v_res_1955_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_args_1956_: *mut lean_object) -> *mut lean_object{
let mut v___x_1958_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1959_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1960_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1961_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1962_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1963_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1964_: *mut lean_object = core::ptr::null_mut(); let mut v_size_1965_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1966_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1967_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1968_: u8 = 0; let mut v___x_1969_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1970_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1971_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1972_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1973_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1974_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1975_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1976_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1977_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1978_: *mut lean_object = core::ptr::null_mut(); let mut v_seed_1979_: u64 = 0; let mut v___x_1980_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1981_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1982_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1983_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1984_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1985_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1986_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1987_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1988_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1989_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1990_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1991_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1992_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1993_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1994_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1995_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1996_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1997_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1998_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1999_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2000_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2001_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2002_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2003_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2004_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2005_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2006_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2007_: *mut lean_object = core::ptr::null_mut(); let mut v_benches_2008_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2009_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2010_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2012_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2013_: u8 = 0; let mut v___x_2015_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_2016_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_2017_: u8 = 0; let mut v_unused_2018_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_1958_ = lean_mk_string_unchecked(b"""\0".as_ptr().cast(), 0, 0);
v___x_1959_ = lean_unsigned_to_nat(0);
v___x_1960_ = l_List_get_x21Internal___redArg(v___x_1958_, v_args_1956_, v___x_1959_);
v___x_1961_ = lean_unsigned_to_nat(1);
v___x_1962_ = l_List_get_x21Internal___redArg(v___x_1958_, v_args_1956_, v___x_1961_);
lean_dec(v_args_1956_);
lean_dec_ref(v___x_1958_);
v___x_1963_ = lean_string_utf8_byte_size(v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1959_);
lean_ctor_set(v___x_1964_, 2, v___x_1963_);
v_size_1965_ = l_String_Slice_toNat_x21(v___x_1964_);
lean_dec_ref_known(v___x_1964_, 3);
v___x_1966_ = lean_unsigned_to_nat(100);
v___x_1967_ = lean_nat_mod(v_size_1965_, v___x_1966_);
v___x_1968_ = lean_nat_dec_eq(v___x_1967_, v___x_1959_);
lean_dec(v___x_1967_);
if v___x_1968_ == 0 {
let mut v___x_1969_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1970_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1971_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1972_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1973_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1974_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1975_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_size_1965_);
lean_dec(v___x_1960_);
v___x_1969_ = lean_mk_string_unchecked(b""phashmap"\0".as_ptr().cast(), 8, 8);
v___x_1970_ = lean_mk_string_unchecked(b""main"\0".as_ptr().cast(), 4, 4);
v___x_1971_ = lean_unsigned_to_nat(166);
v___x_1972_ = lean_unsigned_to_nat(2);
v___x_1973_ = lean_mk_string_unchecked(b""assertion violation: size % REP == 0\n  "\0".as_ptr().cast(), 39, 39);
v___x_1974_ = l_mkPanicMessageWithDecl(v___x_1969_, v___x_1970_, v___x_1971_, v___x_1972_, v___x_1973_);
lean_dec_ref(v___x_1973_);
lean_dec_ref(v___x_1970_);
lean_dec_ref(v___x_1969_);
v___x_1975_ = l_panic___at___00main_spec__0(v___x_1974_);
return v___x_1975_;
} else {
let mut v___x_1976_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1977_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1978_: *mut lean_object = core::ptr::null_mut(); let mut v_seed_1979_: u64 = 0; let mut v___x_1980_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1981_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1982_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1983_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1984_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1985_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1986_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1987_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1988_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1989_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1990_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1991_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1992_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1993_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1994_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1995_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1996_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1997_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1998_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1999_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2000_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2001_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2002_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2003_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2004_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2005_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2006_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2007_: *mut lean_object = core::ptr::null_mut(); let mut v_benches_2008_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2009_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2010_: *mut lean_object = core::ptr::null_mut(); 
v___x_1976_ = lean_string_utf8_byte_size(v___x_1960_);
v___x_1977_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_1977_, 0, v___x_1960_);
lean_ctor_set(v___x_1977_, 1, v___x_1959_);
lean_ctor_set(v___x_1977_, 2, v___x_1976_);
v___x_1978_ = l_String_Slice_toNat_x21(v___x_1977_);
lean_dec_ref_known(v___x_1977_, 3);
v_seed_1979_ = lean_uint64_of_nat(v___x_1978_);
lean_dec(v___x_1978_);
v___x_1980_ = lean_mk_string_unchecked(b""containsHit"\0".as_ptr().cast(), 11, 11);
v___x_1981_ = lean_alloc_closure(l_benchContainsHit___boxed as *mut core::ffi::c_void, 3, 0);
v___x_1982_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_mk_string_unchecked(b""containsMiss"\0".as_ptr().cast(), 12, 12);
v___x_1984_ = lean_alloc_closure(l_benchContainsMiss___boxed as *mut core::ffi::c_void, 3, 0);
v___x_1985_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_mk_string_unchecked(b""iterate"\0".as_ptr().cast(), 7, 7);
v___x_1987_ = lean_alloc_closure(l_benchIterate___boxed as *mut core::ffi::c_void, 3, 0);
v___x_1988_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_mk_string_unchecked(b""insertHit"\0".as_ptr().cast(), 9, 9);
v___x_1990_ = lean_alloc_closure(l_benchInsertHit___boxed as *mut core::ffi::c_void, 3, 0);
v___x_1991_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_mk_string_unchecked(b""insertMissEmpty"\0".as_ptr().cast(), 15, 15);
v___x_1993_ = lean_alloc_closure(l_benchInsertMissEmpty___boxed as *mut core::ffi::c_void, 3, 0);
v___x_1994_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_mk_string_unchecked(b""insertMissEmptyShared"\0".as_ptr().cast(), 21, 21);
v___x_1996_ = lean_alloc_closure(l_benchInsertMissEmptyShared___boxed as *mut core::ffi::c_void, 3, 0);
v___x_1997_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_mk_string_unchecked(b""eraseInsert"\0".as_ptr().cast(), 11, 11);
v___x_1999_ = lean_alloc_closure(l_benchEraseInsert___boxed as *mut core::ffi::c_void, 3, 0);
v___x_2000_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_2000_, 0, v___x_1998_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = lean_box(0);
v___x_2002_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2003_, 0, v___x_1997_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2004_, 0, v___x_1994_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2005_, 0, v___x_1991_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2006_, 0, v___x_1988_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_2007_, 0, v___x_1985_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v_benches_2008_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_benches_2008_, 0, v___x_1982_);
lean_ctor_set(v_benches_2008_, 1, v___x_2007_);
v___x_2009_ = lean_box(0);
v___x_2010_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_seed_1979_, v_size_1965_, v_benches_2008_, v___x_2009_);
lean_dec_ref_known(v_benches_2008_, 2);
if lean_obj_tag(v___x_2010_) == 0 {
let mut v___x_2012_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_2013_: u8 = 0; let mut v_isSharedCheck_2017_: u8 = 0; 
v_isSharedCheck_2017_ = (!lean_is_exclusive(v___x_2010_)) as u8;
if v_isSharedCheck_2017_ == 0 {
let mut v_unused_2018_: *mut lean_object = core::ptr::null_mut(); 
v_unused_2018_ = lean_ctor_get(v___x_2010_, 0);
lean_dec(v_unused_2018_);
v___x_2012_ = v___x_2010_;
v_isShared_2013_ = v_isSharedCheck_2017_;
state = 1; continue;
} else {
lean_dec(v___x_2010_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
state = 1; continue;
}
} else {
return v___x_2010_;
}
}
}
1 => {
if v_isShared_2013_ == 0 {
lean_ctor_set(v___x_2012_, 0, v___x_2009_);
v___x_2015_ = v___x_2012_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_2016_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2009_);
v___x_2015_ = v_reuseFailAlloc_2016_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_args_2019_: *mut lean_object, mut v_a_2020_: *mut lean_object) -> *mut lean_object{
let mut v_res_2021_: *mut lean_object = core::ptr::null_mut(); 
v_res_2021_ = _lean_main(v_args_2019_);
return v_res_2021_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00main_spec__2(mut v_seed_2022_: u64, mut v_size_2023_: *mut lean_object, mut v_as_2024_: *mut lean_object, mut v_as_x27_2025_: *mut lean_object, mut v_b_2026_: *mut lean_object, mut v_a_2027_: *mut lean_object) -> *mut lean_object{
let mut v___x_2029_: *mut lean_object = core::ptr::null_mut(); 
v___x_2029_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_seed_2022_, v_size_2023_, v_as_x27_2025_, v_b_2026_);
return v___x_2029_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00main_spec__2___boxed(mut v_seed_2030_: *mut lean_object, mut v_size_2031_: *mut lean_object, mut v_as_2032_: *mut lean_object, mut v_as_x27_2033_: *mut lean_object, mut v_b_2034_: *mut lean_object, mut v_a_2035_: *mut lean_object, mut v___y_2036_: *mut lean_object) -> *mut lean_object{
let mut v_seed_boxed_2037_: u64 = 0; let mut v_res_2038_: *mut lean_object = core::ptr::null_mut(); 
v_seed_boxed_2037_ = lean_unbox_uint64(v_seed_2030_);
lean_dec_ref(v_seed_2030_);
v_res_2038_ = l_List_forIn_x27_loop___at___00main_spec__2(v_seed_boxed_2037_, v_size_2031_, v_as_2032_, v_as_x27_2033_, v_b_2034_, v_a_2035_);
lean_dec(v_as_x27_2033_);
lean_dec(v_as_2032_);
return v_res_2038_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_PersistentHashMap(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Std_Data_Iterators(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_phashmap(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashMap(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Std_Data_Iterators(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_REP = _init_l_REP();
lean_mark_persistent(l_REP);
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
  lean_initialize();
  let res = initialize_phashmap(1 /* builtin */);
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
