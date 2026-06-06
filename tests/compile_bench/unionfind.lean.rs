// Lean compiler output
// Module: unionfind
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_fget_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_set(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_List_head_x21___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_write___redArg___closed__0_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_write___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_write___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_findEntryAux___closed__0_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [111, 117, 116, 32, 111, 102, 32, 102, 117, 101, 108, 0]};
static mut l_findEntryAux___closed__0: *mut lean_object = core::ptr::addr_of!(l_findEntryAux___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_findEntryAux___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_findEntryAux___closed__0_value) as *mut lean_object] };
static mut l_findEntryAux___closed__1: *mut lean_object = core::ptr::addr_of!(l_findEntryAux___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_findEntryAux___closed__2_value: lean_string_object<13> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 78, 111, 100, 101, 0]};
static mut l_findEntryAux___closed__2: *mut lean_object = core::ptr::addr_of!(l_findEntryAux___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_findEntryAux___closed__3_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_findEntryAux___closed__2_value) as *mut lean_object] };
static mut l_findEntryAux___closed__3: *mut lean_object = core::ptr::addr_of!(l_findEntryAux___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_checkEq___closed__0_value: lean_string_object<20> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [110, 111, 100, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 101, 113, 117, 97, 108, 0]};
static mut l_checkEq___closed__0: *mut lean_object = core::ptr::addr_of!(l_checkEq___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_checkEq___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_checkEq___closed__0_value) as *mut lean_object] };
static mut l_checkEq___closed__1: *mut lean_object = core::ptr::addr_of!(l_checkEq___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_test___closed__0_value: lean_string_object<29> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [105, 110, 112, 117, 116, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 114, 101, 97, 116, 101, 114, 32, 116, 104, 97, 110, 32, 49, 0]};
static mut l_test___closed__0: *mut lean_object = core::ptr::addr_of!(l_test___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_test___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_test___closed__0_value) as *mut lean_object] };
static mut l_test___closed__1: *mut lean_object = core::ptr::addr_of!(l_test___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [69, 114, 114, 111, 114, 32, 58, 32, 0]};
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 107, 32, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_main___boxed__const__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_pure___redArg(mut v_inst_1_: *mut lean_object, mut v_a_2_: *mut lean_object, mut v_s_3_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_7_: u8 = 0; let mut v_toPure_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_12_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_13_: u8 = 0; let mut v_unused_14_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_4_ = lean_ctor_get(v_inst_1_, 0);
v_isSharedCheck_13_ = (!lean_is_exclusive(v_inst_1_)) as u8;
if v_isSharedCheck_13_ == 0 {
let mut v_unused_14_: *mut lean_object = core::ptr::null_mut(); 
v_unused_14_ = lean_ctor_get(v_inst_1_, 1);
lean_dec(v_unused_14_);
v___x_6_ = v_inst_1_;
v_isShared_7_ = v_isSharedCheck_13_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_4_);
lean_dec(v_inst_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_13_;
state = 1; continue;
}
}
1 => {
v_toPure_8_ = lean_ctor_get(v_toApplicative_4_, 1);
lean_inc(v_toPure_8_);
lean_dec_ref(v_toApplicative_4_);
if v_isShared_7_ == 0 {
lean_ctor_set(v___x_6_, 1, v_s_3_);
lean_ctor_set(v___x_6_, 0, v_a_2_);
v___x_10_ = v___x_6_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_12_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_a_2_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v_s_3_);
v___x_10_ = v_reuseFailAlloc_12_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_pure(mut v_m_15_: *mut lean_object, mut v_inst_16_: *mut lean_object, mut v_00_u03c3_17_: *mut lean_object, mut v_00_u03b1_18_: *mut lean_object, mut v_a_19_: *mut lean_object, mut v_s_20_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_24_: u8 = 0; let mut v_toPure_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_29_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_30_: u8 = 0; let mut v_unused_31_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_21_ = lean_ctor_get(v_inst_16_, 0);
v_isSharedCheck_30_ = (!lean_is_exclusive(v_inst_16_)) as u8;
if v_isSharedCheck_30_ == 0 {
let mut v_unused_31_: *mut lean_object = core::ptr::null_mut(); 
v_unused_31_ = lean_ctor_get(v_inst_16_, 1);
lean_dec(v_unused_31_);
v___x_23_ = v_inst_16_;
v_isShared_24_ = v_isSharedCheck_30_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_21_);
lean_dec(v_inst_16_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_30_;
state = 1; continue;
}
}
1 => {
v_toPure_25_ = lean_ctor_get(v_toApplicative_21_, 1);
lean_inc(v_toPure_25_);
lean_dec_ref(v_toApplicative_21_);
if v_isShared_24_ == 0 {
lean_ctor_set(v___x_23_, 1, v_s_20_);
lean_ctor_set(v___x_23_, 0, v_a_19_);
v___x_27_ = v___x_23_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_29_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_19_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_s_20_);
v___x_27_ = v_reuseFailAlloc_29_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_bind___redArg___lam__0(mut v_f_32_: *mut lean_object, mut v_____x_33_: *mut lean_object) -> *mut lean_object{
let mut v_fst_34_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); 
v_fst_34_ = lean_ctor_get(v_____x_33_, 0);
lean_inc(v_fst_34_);
v_snd_35_ = lean_ctor_get(v_____x_33_, 1);
lean_inc(v_snd_35_);
lean_dec_ref(v_____x_33_);
v___x_36_ = lean_apply_2(v_f_32_, v_fst_34_, v_snd_35_);
return v___x_36_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_bind___redArg(mut v_inst_37_: *mut lean_object, mut v_x_38_: *mut lean_object, mut v_f_39_: *mut lean_object, mut v_s_40_: *mut lean_object) -> *mut lean_object{
let mut v_toBind_41_: *mut lean_object = core::ptr::null_mut(); let mut v___f_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
v_toBind_41_ = lean_ctor_get(v_inst_37_, 1);
lean_inc(v_toBind_41_);
lean_dec_ref(v_inst_37_);
v___f_42_ = lean_alloc_closure(l_StateT_x27_bind___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_42_, 0, v_f_39_);
v___x_43_ = lean_apply_1(v_x_38_, v_s_40_);
v___x_44_ = lean_apply_4(v_toBind_41_, lean_box(0), lean_box(0), v___x_43_, v___f_42_);
return v___x_44_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_bind(mut v_m_45_: *mut lean_object, mut v_inst_46_: *mut lean_object, mut v_00_u03c3_47_: *mut lean_object, mut v_00_u03b1_48_: *mut lean_object, mut v_00_u03b2_49_: *mut lean_object, mut v_x_50_: *mut lean_object, mut v_f_51_: *mut lean_object, mut v_s_52_: *mut lean_object) -> *mut lean_object{
let mut v_toBind_53_: *mut lean_object = core::ptr::null_mut(); let mut v___f_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); 
v_toBind_53_ = lean_ctor_get(v_inst_46_, 1);
lean_inc(v_toBind_53_);
lean_dec_ref(v_inst_46_);
v___f_54_ = lean_alloc_closure(l_StateT_x27_bind___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_54_, 0, v_f_51_);
v___x_55_ = lean_apply_1(v_x_50_, v_s_52_);
v___x_56_ = lean_apply_4(v_toBind_53_, lean_box(0), lean_box(0), v___x_55_, v___f_54_);
return v___x_56_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_read___redArg(mut v_inst_57_: *mut lean_object, mut v_s_58_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_62_: u8 = 0; let mut v_toPure_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_67_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_68_: u8 = 0; let mut v_unused_69_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_59_ = lean_ctor_get(v_inst_57_, 0);
v_isSharedCheck_68_ = (!lean_is_exclusive(v_inst_57_)) as u8;
if v_isSharedCheck_68_ == 0 {
let mut v_unused_69_: *mut lean_object = core::ptr::null_mut(); 
v_unused_69_ = lean_ctor_get(v_inst_57_, 1);
lean_dec(v_unused_69_);
v___x_61_ = v_inst_57_;
v_isShared_62_ = v_isSharedCheck_68_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_59_);
lean_dec(v_inst_57_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_68_;
state = 1; continue;
}
}
1 => {
v_toPure_63_ = lean_ctor_get(v_toApplicative_59_, 1);
lean_inc(v_toPure_63_);
lean_dec_ref(v_toApplicative_59_);
lean_inc(v_s_58_);
if v_isShared_62_ == 0 {
lean_ctor_set(v___x_61_, 1, v_s_58_);
lean_ctor_set(v___x_61_, 0, v_s_58_);
v___x_65_ = v___x_61_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_67_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_s_58_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_s_58_);
v___x_65_ = v_reuseFailAlloc_67_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_read(mut v_m_70_: *mut lean_object, mut v_inst_71_: *mut lean_object, mut v_00_u03c3_72_: *mut lean_object, mut v_s_73_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_77_: u8 = 0; let mut v_toPure_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_82_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_83_: u8 = 0; let mut v_unused_84_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_74_ = lean_ctor_get(v_inst_71_, 0);
v_isSharedCheck_83_ = (!lean_is_exclusive(v_inst_71_)) as u8;
if v_isSharedCheck_83_ == 0 {
let mut v_unused_84_: *mut lean_object = core::ptr::null_mut(); 
v_unused_84_ = lean_ctor_get(v_inst_71_, 1);
lean_dec(v_unused_84_);
v___x_76_ = v_inst_71_;
v_isShared_77_ = v_isSharedCheck_83_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_74_);
lean_dec(v_inst_71_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_83_;
state = 1; continue;
}
}
1 => {
v_toPure_78_ = lean_ctor_get(v_toApplicative_74_, 1);
lean_inc(v_toPure_78_);
lean_dec_ref(v_toApplicative_74_);
lean_inc(v_s_73_);
if v_isShared_77_ == 0 {
lean_ctor_set(v___x_76_, 1, v_s_73_);
lean_ctor_set(v___x_76_, 0, v_s_73_);
v___x_80_ = v___x_76_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_82_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_s_73_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_s_73_);
v___x_80_ = v_reuseFailAlloc_82_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_write___redArg(mut v_inst_85_: *mut lean_object, mut v_s_x27_86_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_90_: u8 = 0; let mut v_toPure_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_96_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_97_: u8 = 0; let mut v_unused_98_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_87_ = lean_ctor_get(v_inst_85_, 0);
v_isSharedCheck_97_ = (!lean_is_exclusive(v_inst_85_)) as u8;
if v_isSharedCheck_97_ == 0 {
let mut v_unused_98_: *mut lean_object = core::ptr::null_mut(); 
v_unused_98_ = lean_ctor_get(v_inst_85_, 1);
lean_dec(v_unused_98_);
v___x_89_ = v_inst_85_;
v_isShared_90_ = v_isSharedCheck_97_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_87_);
lean_dec(v_inst_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_97_;
state = 1; continue;
}
}
1 => {
v_toPure_91_ = lean_ctor_get(v_toApplicative_87_, 1);
lean_inc(v_toPure_91_);
lean_dec_ref(v_toApplicative_87_);
v___x_92_ = lean_box(0);
if v_isShared_90_ == 0 {
lean_ctor_set(v___x_89_, 1, v_s_x27_86_);
lean_ctor_set(v___x_89_, 0, v___x_92_);
v___x_94_ = v___x_89_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_96_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_s_x27_86_);
v___x_94_ = v_reuseFailAlloc_96_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_write(mut v_m_99_: *mut lean_object, mut v_inst_100_: *mut lean_object, mut v_00_u03c3_101_: *mut lean_object, mut v_s_x27_102_: *mut lean_object, mut v_s_103_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_107_: u8 = 0; let mut v_toPure_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_113_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_114_: u8 = 0; let mut v_unused_115_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_104_ = lean_ctor_get(v_inst_100_, 0);
v_isSharedCheck_114_ = (!lean_is_exclusive(v_inst_100_)) as u8;
if v_isSharedCheck_114_ == 0 {
let mut v_unused_115_: *mut lean_object = core::ptr::null_mut(); 
v_unused_115_ = lean_ctor_get(v_inst_100_, 1);
lean_dec(v_unused_115_);
v___x_106_ = v_inst_100_;
v_isShared_107_ = v_isSharedCheck_114_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_104_);
lean_dec(v_inst_100_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_114_;
state = 1; continue;
}
}
1 => {
v_toPure_108_ = lean_ctor_get(v_toApplicative_104_, 1);
lean_inc(v_toPure_108_);
lean_dec_ref(v_toApplicative_104_);
v___x_109_ = lean_box(0);
if v_isShared_107_ == 0 {
lean_ctor_set(v___x_106_, 1, v_s_x27_102_);
lean_ctor_set(v___x_106_, 0, v___x_109_);
v___x_111_ = v___x_106_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_113_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_s_x27_102_);
v___x_111_ = v_reuseFailAlloc_113_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_write___boxed(mut v_m_116_: *mut lean_object, mut v_inst_117_: *mut lean_object, mut v_00_u03c3_118_: *mut lean_object, mut v_s_x27_119_: *mut lean_object, mut v_s_120_: *mut lean_object) -> *mut lean_object{
let mut v_res_121_: *mut lean_object = core::ptr::null_mut(); 
v_res_121_ = l_StateT_x27_write(v_m_116_, v_inst_117_, v_00_u03c3_118_, v_s_x27_119_, v_s_120_);
lean_dec(v_s_120_);
return v_res_121_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_updt___redArg(mut v_inst_122_: *mut lean_object, mut v_f_123_: *mut lean_object, mut v_s_124_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_128_: u8 = 0; let mut v_toPure_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_135_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_136_: u8 = 0; let mut v_unused_137_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_125_ = lean_ctor_get(v_inst_122_, 0);
v_isSharedCheck_136_ = (!lean_is_exclusive(v_inst_122_)) as u8;
if v_isSharedCheck_136_ == 0 {
let mut v_unused_137_: *mut lean_object = core::ptr::null_mut(); 
v_unused_137_ = lean_ctor_get(v_inst_122_, 1);
lean_dec(v_unused_137_);
v___x_127_ = v_inst_122_;
v_isShared_128_ = v_isSharedCheck_136_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_125_);
lean_dec(v_inst_122_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_136_;
state = 1; continue;
}
}
1 => {
v_toPure_129_ = lean_ctor_get(v_toApplicative_125_, 1);
lean_inc(v_toPure_129_);
lean_dec_ref(v_toApplicative_125_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_f_123_, v_s_124_);
if v_isShared_128_ == 0 {
lean_ctor_set(v___x_127_, 1, v___x_131_);
lean_ctor_set(v___x_127_, 0, v___x_130_);
v___x_133_ = v___x_127_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_135_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_135_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_updt(mut v_m_138_: *mut lean_object, mut v_inst_139_: *mut lean_object, mut v_00_u03c3_140_: *mut lean_object, mut v_f_141_: *mut lean_object, mut v_s_142_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_146_: u8 = 0; let mut v_toPure_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_153_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_154_: u8 = 0; let mut v_unused_155_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_toApplicative_143_ = lean_ctor_get(v_inst_139_, 0);
v_isSharedCheck_154_ = (!lean_is_exclusive(v_inst_139_)) as u8;
if v_isSharedCheck_154_ == 0 {
let mut v_unused_155_: *mut lean_object = core::ptr::null_mut(); 
v_unused_155_ = lean_ctor_get(v_inst_139_, 1);
lean_dec(v_unused_155_);
v___x_145_ = v_inst_139_;
v_isShared_146_ = v_isSharedCheck_154_;
state = 1; continue;
} else {
lean_inc(v_toApplicative_143_);
lean_dec(v_inst_139_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_154_;
state = 1; continue;
}
}
1 => {
v_toPure_147_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_147_);
lean_dec_ref(v_toApplicative_143_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_apply_1(v_f_141_, v_s_142_);
if v_isShared_146_ == 0 {
lean_ctor_set(v___x_145_, 1, v___x_149_);
lean_ctor_set(v___x_145_, 0, v___x_148_);
v___x_151_ = v___x_145_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_153_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_153_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__0(mut v_toApplicative_156_: *mut lean_object, mut v_f_157_: *mut lean_object, mut v_____x_158_: *mut lean_object) -> *mut lean_object{
let mut v_fst_159_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_163_: u8 = 0; let mut v_toPure_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_169_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_170_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_159_ = lean_ctor_get(v_____x_158_, 0);
v_snd_160_ = lean_ctor_get(v_____x_158_, 1);
v_isSharedCheck_170_ = (!lean_is_exclusive(v_____x_158_)) as u8;
if v_isSharedCheck_170_ == 0 {
v___x_162_ = v_____x_158_;
v_isShared_163_ = v_isSharedCheck_170_;
state = 1; continue;
} else {
lean_inc(v_snd_160_);
lean_inc(v_fst_159_);
lean_dec(v_____x_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_170_;
state = 1; continue;
}
}
1 => {
v_toPure_164_ = lean_ctor_get(v_toApplicative_156_, 1);
lean_inc(v_toPure_164_);
lean_dec_ref(v_toApplicative_156_);
v___x_165_ = lean_apply_1(v_f_157_, v_fst_159_);
if v_isShared_163_ == 0 {
lean_ctor_set(v___x_162_, 0, v___x_165_);
v___x_167_ = v___x_162_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_169_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_snd_160_);
v___x_167_ = v_reuseFailAlloc_169_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__1(mut v_inst_171_: *mut lean_object, mut v_00_u03b1_172_: *mut lean_object, mut v_00_u03b2_173_: *mut lean_object, mut v_f_174_: *mut lean_object, mut v_x_175_: *mut lean_object, mut v___y_176_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_177_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_178_: *mut lean_object = core::ptr::null_mut(); let mut v___f_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_177_ = lean_ctor_get(v_inst_171_, 0);
lean_inc_ref(v_toApplicative_177_);
v_toBind_178_ = lean_ctor_get(v_inst_171_, 1);
lean_inc(v_toBind_178_);
lean_dec_ref(v_inst_171_);
v___f_179_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_179_, 0, v_toApplicative_177_);
lean_closure_set(v___f_179_, 1, v_f_174_);
v___x_180_ = lean_apply_1(v_x_175_, v___y_176_);
v___x_181_ = lean_apply_4(v_toBind_178_, lean_box(0), lean_box(0), v___x_180_, v___f_179_);
return v___x_181_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__2(mut v_toApplicative_182_: *mut lean_object, mut v___y_183_: *mut lean_object, mut v_____x_184_: *mut lean_object) -> *mut lean_object{
let mut v_snd_185_: *mut lean_object = core::ptr::null_mut(); let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_188_: u8 = 0; let mut v_toPure_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_193_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_194_: u8 = 0; let mut v_unused_195_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_snd_185_ = lean_ctor_get(v_____x_184_, 1);
v_isSharedCheck_194_ = (!lean_is_exclusive(v_____x_184_)) as u8;
if v_isSharedCheck_194_ == 0 {
let mut v_unused_195_: *mut lean_object = core::ptr::null_mut(); 
v_unused_195_ = lean_ctor_get(v_____x_184_, 0);
lean_dec(v_unused_195_);
v___x_187_ = v_____x_184_;
v_isShared_188_ = v_isSharedCheck_194_;
state = 1; continue;
} else {
lean_inc(v_snd_185_);
lean_dec(v_____x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_194_;
state = 1; continue;
}
}
1 => {
v_toPure_189_ = lean_ctor_get(v_toApplicative_182_, 1);
lean_inc(v_toPure_189_);
lean_dec_ref(v_toApplicative_182_);
if v_isShared_188_ == 0 {
lean_ctor_set(v___x_187_, 0, v___y_183_);
v___x_191_ = v___x_187_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_193_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___y_183_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_snd_185_);
v___x_191_ = v_reuseFailAlloc_193_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__3(mut v_inst_196_: *mut lean_object, mut v_00_u03b1_197_: *mut lean_object, mut v_00_u03b2_198_: *mut lean_object, mut v___y_199_: *mut lean_object, mut v___y_200_: *mut lean_object, mut v___y_201_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_202_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_203_: *mut lean_object = core::ptr::null_mut(); let mut v___f_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_202_ = lean_ctor_get(v_inst_196_, 0);
lean_inc_ref(v_toApplicative_202_);
v_toBind_203_ = lean_ctor_get(v_inst_196_, 1);
lean_inc(v_toBind_203_);
lean_dec_ref(v_inst_196_);
v___f_204_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_204_, 0, v_toApplicative_202_);
lean_closure_set(v___f_204_, 1, v___y_199_);
v___x_205_ = lean_apply_1(v___y_200_, v___y_201_);
v___x_206_ = lean_apply_4(v_toBind_203_, lean_box(0), lean_box(0), v___x_205_, v___f_204_);
return v___x_206_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__4(mut v_toApplicative_207_: *mut lean_object, mut v_fst_208_: *mut lean_object, mut v_____x_209_: *mut lean_object) -> *mut lean_object{
let mut v_fst_210_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_214_: u8 = 0; let mut v_toPure_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_220_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_221_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_fst_210_ = lean_ctor_get(v_____x_209_, 0);
v_snd_211_ = lean_ctor_get(v_____x_209_, 1);
v_isSharedCheck_221_ = (!lean_is_exclusive(v_____x_209_)) as u8;
if v_isSharedCheck_221_ == 0 {
v___x_213_ = v_____x_209_;
v_isShared_214_ = v_isSharedCheck_221_;
state = 1; continue;
} else {
lean_inc(v_snd_211_);
lean_inc(v_fst_210_);
lean_dec(v_____x_209_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_221_;
state = 1; continue;
}
}
1 => {
v_toPure_215_ = lean_ctor_get(v_toApplicative_207_, 1);
lean_inc(v_toPure_215_);
lean_dec_ref(v_toApplicative_207_);
v___x_216_ = lean_apply_1(v_fst_208_, v_fst_210_);
if v_isShared_214_ == 0 {
lean_ctor_set(v___x_213_, 0, v___x_216_);
v___x_218_ = v___x_213_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_220_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_snd_211_);
v___x_218_ = v_reuseFailAlloc_220_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__5(mut v_toApplicative_222_: *mut lean_object, mut v_x_223_: *mut lean_object, mut v_toBind_224_: *mut lean_object, mut v_____x_225_: *mut lean_object) -> *mut lean_object{
let mut v_fst_226_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_227_: *mut lean_object = core::ptr::null_mut(); let mut v___f_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); 
v_fst_226_ = lean_ctor_get(v_____x_225_, 0);
lean_inc(v_fst_226_);
v_snd_227_ = lean_ctor_get(v_____x_225_, 1);
lean_inc(v_snd_227_);
lean_dec_ref(v_____x_225_);
v___f_228_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__4 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_228_, 0, v_toApplicative_222_);
lean_closure_set(v___f_228_, 1, v_fst_226_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_apply_2(v_x_223_, v___x_229_, v_snd_227_);
v___x_231_ = lean_apply_4(v_toBind_224_, lean_box(0), lean_box(0), v___x_230_, v___f_228_);
return v___x_231_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__6(mut v_inst_232_: *mut lean_object, mut v_00_u03b1_233_: *mut lean_object, mut v_00_u03b2_234_: *mut lean_object, mut v_f_235_: *mut lean_object, mut v_x_236_: *mut lean_object, mut v___y_237_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_238_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_239_: *mut lean_object = core::ptr::null_mut(); let mut v___f_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_241_: *mut lean_object = core::ptr::null_mut(); let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_238_ = lean_ctor_get(v_inst_232_, 0);
lean_inc_ref(v_toApplicative_238_);
v_toBind_239_ = lean_ctor_get(v_inst_232_, 1);
lean_inc_n(v_toBind_239_, 2);
lean_dec_ref(v_inst_232_);
v___f_240_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__5 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_240_, 0, v_toApplicative_238_);
lean_closure_set(v___f_240_, 1, v_x_236_);
lean_closure_set(v___f_240_, 2, v_toBind_239_);
v___x_241_ = lean_apply_1(v_f_235_, v___y_237_);
v___x_242_ = lean_apply_4(v_toBind_239_, lean_box(0), lean_box(0), v___x_241_, v___f_240_);
return v___x_242_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__7(mut v_toApplicative_243_: *mut lean_object, mut v_fst_244_: *mut lean_object, mut v_____x_245_: *mut lean_object) -> *mut lean_object{
let mut v_snd_246_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_249_: u8 = 0; let mut v_toPure_250_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: *mut lean_object = core::ptr::null_mut(); let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_254_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_255_: u8 = 0; let mut v_unused_256_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_snd_246_ = lean_ctor_get(v_____x_245_, 1);
v_isSharedCheck_255_ = (!lean_is_exclusive(v_____x_245_)) as u8;
if v_isSharedCheck_255_ == 0 {
let mut v_unused_256_: *mut lean_object = core::ptr::null_mut(); 
v_unused_256_ = lean_ctor_get(v_____x_245_, 0);
lean_dec(v_unused_256_);
v___x_248_ = v_____x_245_;
v_isShared_249_ = v_isSharedCheck_255_;
state = 1; continue;
} else {
lean_inc(v_snd_246_);
lean_dec(v_____x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_255_;
state = 1; continue;
}
}
1 => {
v_toPure_250_ = lean_ctor_get(v_toApplicative_243_, 1);
lean_inc(v_toPure_250_);
lean_dec_ref(v_toApplicative_243_);
if v_isShared_249_ == 0 {
lean_ctor_set(v___x_248_, 0, v_fst_244_);
v___x_252_ = v___x_248_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_254_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_fst_244_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_snd_246_);
v___x_252_ = v_reuseFailAlloc_254_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__8(mut v_toApplicative_257_: *mut lean_object, mut v_y_258_: *mut lean_object, mut v_toBind_259_: *mut lean_object, mut v_____x_260_: *mut lean_object) -> *mut lean_object{
let mut v_fst_261_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_262_: *mut lean_object = core::ptr::null_mut(); let mut v___f_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); 
v_fst_261_ = lean_ctor_get(v_____x_260_, 0);
lean_inc(v_fst_261_);
v_snd_262_ = lean_ctor_get(v_____x_260_, 1);
lean_inc(v_snd_262_);
lean_dec_ref(v_____x_260_);
v___f_263_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__7 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_263_, 0, v_toApplicative_257_);
lean_closure_set(v___f_263_, 1, v_fst_261_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_apply_2(v_y_258_, v___x_264_, v_snd_262_);
v___x_266_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_265_, v___f_263_);
return v___x_266_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__9(mut v_inst_267_: *mut lean_object, mut v_00_u03b1_268_: *mut lean_object, mut v_00_u03b2_269_: *mut lean_object, mut v_x_270_: *mut lean_object, mut v_y_271_: *mut lean_object, mut v___y_272_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_273_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_274_: *mut lean_object = core::ptr::null_mut(); let mut v___f_275_: *mut lean_object = core::ptr::null_mut(); let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); let mut v___x_277_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_273_ = lean_ctor_get(v_inst_267_, 0);
lean_inc_ref(v_toApplicative_273_);
v_toBind_274_ = lean_ctor_get(v_inst_267_, 1);
lean_inc_n(v_toBind_274_, 2);
lean_dec_ref(v_inst_267_);
v___f_275_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__8 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_275_, 0, v_toApplicative_273_);
lean_closure_set(v___f_275_, 1, v_y_271_);
lean_closure_set(v___f_275_, 2, v_toBind_274_);
v___x_276_ = lean_apply_1(v_x_270_, v___y_272_);
v___x_277_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_276_, v___f_275_);
return v___x_277_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__10(mut v_y_278_: *mut lean_object, mut v_____x_279_: *mut lean_object) -> *mut lean_object{
let mut v_snd_280_: *mut lean_object = core::ptr::null_mut(); let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); 
v_snd_280_ = lean_ctor_get(v_____x_279_, 1);
lean_inc(v_snd_280_);
lean_dec_ref(v_____x_279_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_apply_2(v_y_278_, v___x_281_, v_snd_280_);
return v___x_282_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg___lam__11(mut v_inst_283_: *mut lean_object, mut v_00_u03b1_284_: *mut lean_object, mut v_00_u03b2_285_: *mut lean_object, mut v_x_286_: *mut lean_object, mut v_y_287_: *mut lean_object, mut v___y_288_: *mut lean_object) -> *mut lean_object{
let mut v_toBind_289_: *mut lean_object = core::ptr::null_mut(); let mut v___f_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: *mut lean_object = core::ptr::null_mut(); 
v_toBind_289_ = lean_ctor_get(v_inst_283_, 1);
lean_inc(v_toBind_289_);
lean_dec_ref(v_inst_283_);
v___f_290_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__10 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_290_, 0, v_y_287_);
v___x_291_ = lean_apply_1(v_x_286_, v___y_288_);
v___x_292_ = lean_apply_4(v_toBind_289_, lean_box(0), lean_box(0), v___x_291_, v___f_290_);
return v___x_292_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad___redArg(mut v_inst_293_: *mut lean_object) -> *mut lean_object{
let mut v___f_294_: *mut lean_object = core::ptr::null_mut(); let mut v___f_295_: *mut lean_object = core::ptr::null_mut(); let mut v___f_296_: *mut lean_object = core::ptr::null_mut(); let mut v___f_297_: *mut lean_object = core::ptr::null_mut(); let mut v___f_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_303_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref_n(v_inst_293_, 6);
v___f_294_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_294_, 0, v_inst_293_);
v___f_295_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__3 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_295_, 0, v_inst_293_);
v___f_296_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__6 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_296_, 0, v_inst_293_);
v___f_297_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__9 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_297_, 0, v_inst_293_);
v___f_298_ = lean_alloc_closure(l_StateT_x27_instMonad___redArg___lam__11 as *mut core::ffi::c_void, 6, 1);
lean_closure_set(v___f_298_, 0, v_inst_293_);
v___x_299_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_299_, 0, v___f_294_);
lean_ctor_set(v___x_299_, 1, v___f_295_);
v___x_300_ = lean_alloc_closure(l_StateT_x27_pure as *mut core::ffi::c_void, 6, 3);
lean_closure_set(v___x_300_, 0, lean_box(0));
lean_closure_set(v___x_300_, 1, v_inst_293_);
lean_closure_set(v___x_300_, 2, lean_box(0));
v___x_301_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
lean_ctor_set(v___x_301_, 2, v___f_296_);
lean_ctor_set(v___x_301_, 3, v___f_297_);
lean_ctor_set(v___x_301_, 4, v___f_298_);
v___x_302_ = lean_alloc_closure(l_StateT_x27_bind as *mut core::ffi::c_void, 8, 3);
lean_closure_set(v___x_302_, 0, lean_box(0));
lean_closure_set(v___x_302_, 1, v_inst_293_);
lean_closure_set(v___x_302_, 2, lean_box(0));
v___x_303_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
#[no_mangle] pub unsafe extern "C" fn l_StateT_x27_instMonad(mut v_m_304_: *mut lean_object, mut v_inst_305_: *mut lean_object, mut v_00_u03c3_306_: *mut lean_object) -> *mut lean_object{
let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); 
v___x_307_ = l_StateT_x27_instMonad___redArg(v_inst_305_);
return v___x_307_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_pure___redArg(mut v_inst_308_: *mut lean_object, mut v_a_309_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_310_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_312_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_310_ = lean_ctor_get(v_inst_308_, 0);
lean_inc_ref(v_toApplicative_310_);
lean_dec_ref(v_inst_308_);
v_toPure_311_ = lean_ctor_get(v_toApplicative_310_, 1);
lean_inc(v_toPure_311_);
lean_dec_ref(v_toApplicative_310_);
v___x_312_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_312_, 0, v_a_309_);
v___x_313_ = lean_apply_2(v_toPure_311_, lean_box(0), v___x_312_);
return v___x_313_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_pure(mut v_m_314_: *mut lean_object, mut v_inst_315_: *mut lean_object, mut v_00_u03b5_316_: *mut lean_object, mut v_00_u03b1_317_: *mut lean_object, mut v_a_318_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_319_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_320_: *mut lean_object = core::ptr::null_mut(); let mut v___x_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_319_ = lean_ctor_get(v_inst_315_, 0);
lean_inc_ref(v_toApplicative_319_);
lean_dec_ref(v_inst_315_);
v_toPure_320_ = lean_ctor_get(v_toApplicative_319_, 1);
lean_inc(v_toPure_320_);
lean_dec_ref(v_toApplicative_319_);
v___x_321_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_321_, 0, v_a_318_);
v___x_322_ = lean_apply_2(v_toPure_320_, lean_box(0), v___x_321_);
return v___x_322_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_bind___redArg___lam__0(mut v_toPure_323_: *mut lean_object, mut v_f_324_: *mut lean_object, mut v_v_325_: *mut lean_object) -> *mut lean_object{
let mut v_a_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_329_: u8 = 0; let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_333_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_334_: u8 = 0; let mut v_a_335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_v_325_) == 0 {
let mut v_a_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_329_: u8 = 0; let mut v_isSharedCheck_334_: u8 = 0; 
lean_dec(v_f_324_);
v_a_326_ = lean_ctor_get(v_v_325_, 0);
v_isSharedCheck_334_ = (!lean_is_exclusive(v_v_325_)) as u8;
if v_isSharedCheck_334_ == 0 {
v___x_328_ = v_v_325_;
v_isShared_329_ = v_isSharedCheck_334_;
state = 1; continue;
} else {
lean_inc(v_a_326_);
lean_dec(v_v_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
state = 1; continue;
}
} else {
let mut v_a_335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_toPure_323_);
v_a_335_ = lean_ctor_get(v_v_325_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v_v_325_, 1);
v___x_336_ = lean_apply_1(v_f_324_, v_a_335_);
return v___x_336_;
}
}
1 => {
if v_isShared_329_ == 0 {
v___x_331_ = v___x_328_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_333_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_333_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_bind___redArg(mut v_inst_337_: *mut lean_object, mut v_x_338_: *mut lean_object, mut v_f_339_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_340_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_341_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_342_: *mut lean_object = core::ptr::null_mut(); let mut v___f_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_344_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_340_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_ref(v_toApplicative_340_);
v_toBind_341_ = lean_ctor_get(v_inst_337_, 1);
lean_inc(v_toBind_341_);
lean_dec_ref(v_inst_337_);
v_toPure_342_ = lean_ctor_get(v_toApplicative_340_, 1);
lean_inc(v_toPure_342_);
lean_dec_ref(v_toApplicative_340_);
v___f_343_ = lean_alloc_closure(l_ExceptT_x27_bind___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_343_, 0, v_toPure_342_);
lean_closure_set(v___f_343_, 1, v_f_339_);
v___x_344_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v_x_338_, v___f_343_);
return v___x_344_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_bind(mut v_m_345_: *mut lean_object, mut v_inst_346_: *mut lean_object, mut v_00_u03b5_347_: *mut lean_object, mut v_00_u03b1_348_: *mut lean_object, mut v_00_u03b2_349_: *mut lean_object, mut v_x_350_: *mut lean_object, mut v_f_351_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_352_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_353_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_354_: *mut lean_object = core::ptr::null_mut(); let mut v___f_355_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_352_ = lean_ctor_get(v_inst_346_, 0);
lean_inc_ref(v_toApplicative_352_);
v_toBind_353_ = lean_ctor_get(v_inst_346_, 1);
lean_inc(v_toBind_353_);
lean_dec_ref(v_inst_346_);
v_toPure_354_ = lean_ctor_get(v_toApplicative_352_, 1);
lean_inc(v_toPure_354_);
lean_dec_ref(v_toApplicative_352_);
v___f_355_ = lean_alloc_closure(l_ExceptT_x27_bind___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_355_, 0, v_toPure_354_);
lean_closure_set(v___f_355_, 1, v_f_351_);
v___x_356_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v_x_350_, v___f_355_);
return v___x_356_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_error___redArg(mut v_inst_357_: *mut lean_object, mut v_e_358_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_359_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_361_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_359_ = lean_ctor_get(v_inst_357_, 0);
lean_inc_ref(v_toApplicative_359_);
lean_dec_ref(v_inst_357_);
v_toPure_360_ = lean_ctor_get(v_toApplicative_359_, 1);
lean_inc(v_toPure_360_);
lean_dec_ref(v_toApplicative_359_);
v___x_361_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_361_, 0, v_e_358_);
v___x_362_ = lean_apply_2(v_toPure_360_, lean_box(0), v___x_361_);
return v___x_362_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_error(mut v_m_363_: *mut lean_object, mut v_inst_364_: *mut lean_object, mut v_00_u03b5_365_: *mut lean_object, mut v_00_u03b1_366_: *mut lean_object, mut v_e_367_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_368_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_368_ = lean_ctor_get(v_inst_364_, 0);
lean_inc_ref(v_toApplicative_368_);
lean_dec_ref(v_inst_364_);
v_toPure_369_ = lean_ctor_get(v_toApplicative_368_, 1);
lean_inc(v_toPure_369_);
lean_dec_ref(v_toApplicative_368_);
v___x_370_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_370_, 0, v_e_367_);
v___x_371_ = lean_apply_2(v_toPure_369_, lean_box(0), v___x_370_);
return v___x_371_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_lift___redArg___lam__0(mut v_toPure_372_: *mut lean_object, mut v_a_373_: *mut lean_object) -> *mut lean_object{
let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_375_: *mut lean_object = core::ptr::null_mut(); 
v___x_374_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_374_, 0, v_a_373_);
v___x_375_ = lean_apply_2(v_toPure_372_, lean_box(0), v___x_374_);
return v___x_375_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_lift___redArg(mut v_inst_376_: *mut lean_object, mut v_x_377_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_378_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_379_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_380_: *mut lean_object = core::ptr::null_mut(); let mut v___f_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_378_ = lean_ctor_get(v_inst_376_, 0);
lean_inc_ref(v_toApplicative_378_);
v_toBind_379_ = lean_ctor_get(v_inst_376_, 1);
lean_inc(v_toBind_379_);
lean_dec_ref(v_inst_376_);
v_toPure_380_ = lean_ctor_get(v_toApplicative_378_, 1);
lean_inc(v_toPure_380_);
lean_dec_ref(v_toApplicative_378_);
v___f_381_ = lean_alloc_closure(l_ExceptT_x27_lift___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_381_, 0, v_toPure_380_);
v___x_382_ = lean_apply_4(v_toBind_379_, lean_box(0), lean_box(0), v_x_377_, v___f_381_);
return v___x_382_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_lift(mut v_m_383_: *mut lean_object, mut v_inst_384_: *mut lean_object, mut v_00_u03b5_385_: *mut lean_object, mut v_00_u03b1_386_: *mut lean_object, mut v_x_387_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_388_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_389_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_390_: *mut lean_object = core::ptr::null_mut(); let mut v___f_391_: *mut lean_object = core::ptr::null_mut(); let mut v___x_392_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_388_ = lean_ctor_get(v_inst_384_, 0);
lean_inc_ref(v_toApplicative_388_);
v_toBind_389_ = lean_ctor_get(v_inst_384_, 1);
lean_inc(v_toBind_389_);
lean_dec_ref(v_inst_384_);
v_toPure_390_ = lean_ctor_get(v_toApplicative_388_, 1);
lean_inc(v_toPure_390_);
lean_dec_ref(v_toApplicative_388_);
v___f_391_ = lean_alloc_closure(l_ExceptT_x27_lift___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_391_, 0, v_toPure_390_);
v___x_392_ = lean_apply_4(v_toBind_389_, lean_box(0), lean_box(0), v_x_387_, v___f_391_);
return v___x_392_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__0(mut v_toPure_393_: *mut lean_object, mut v_f_394_: *mut lean_object, mut v_v_395_: *mut lean_object) -> *mut lean_object{
let mut v_a_396_: *mut lean_object = core::ptr::null_mut(); let mut v___x_398_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_399_: u8 = 0; let mut v___x_401_: *mut lean_object = core::ptr::null_mut(); let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_403_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_404_: u8 = 0; let mut v_a_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_408_: u8 = 0; let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); let mut v___x_412_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_413_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_414_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_v_395_) == 0 {
let mut v_a_396_: *mut lean_object = core::ptr::null_mut(); let mut v___x_398_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_399_: u8 = 0; let mut v_isSharedCheck_404_: u8 = 0; 
lean_dec(v_f_394_);
v_a_396_ = lean_ctor_get(v_v_395_, 0);
v_isSharedCheck_404_ = (!lean_is_exclusive(v_v_395_)) as u8;
if v_isSharedCheck_404_ == 0 {
v___x_398_ = v_v_395_;
v_isShared_399_ = v_isSharedCheck_404_;
state = 1; continue;
} else {
lean_inc(v_a_396_);
lean_dec(v_v_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
state = 1; continue;
}
} else {
let mut v_a_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_408_: u8 = 0; let mut v_isSharedCheck_414_: u8 = 0; 
v_a_405_ = lean_ctor_get(v_v_395_, 0);
v_isSharedCheck_414_ = (!lean_is_exclusive(v_v_395_)) as u8;
if v_isSharedCheck_414_ == 0 {
v___x_407_ = v_v_395_;
v_isShared_408_ = v_isSharedCheck_414_;
state = 3; continue;
} else {
lean_inc(v_a_405_);
lean_dec(v_v_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_414_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_399_ == 0 {
v___x_401_ = v___x_398_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_403_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_403_;
state = 2; continue;
}
}
3 => {
v___x_409_ = lean_apply_1(v_f_394_, v_a_405_);
if v_isShared_408_ == 0 {
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_413_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_413_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__1(mut v_inst_415_: *mut lean_object, mut v_00_u03b1_416_: *mut lean_object, mut v_00_u03b2_417_: *mut lean_object, mut v_f_418_: *mut lean_object, mut v_x_419_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_420_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_421_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_422_: *mut lean_object = core::ptr::null_mut(); let mut v___f_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_424_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_420_ = lean_ctor_get(v_inst_415_, 0);
lean_inc_ref(v_toApplicative_420_);
v_toBind_421_ = lean_ctor_get(v_inst_415_, 1);
lean_inc(v_toBind_421_);
lean_dec_ref(v_inst_415_);
v_toPure_422_ = lean_ctor_get(v_toApplicative_420_, 1);
lean_inc(v_toPure_422_);
lean_dec_ref(v_toApplicative_420_);
v___f_423_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_423_, 0, v_toPure_422_);
lean_closure_set(v___f_423_, 1, v_f_418_);
v___x_424_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v_x_419_, v___f_423_);
return v___x_424_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__2(mut v_toPure_425_: *mut lean_object, mut v___y_426_: *mut lean_object, mut v_v_427_: *mut lean_object) -> *mut lean_object{
let mut v_a_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_430_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_431_: u8 = 0; let mut v___x_433_: *mut lean_object = core::ptr::null_mut(); let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_435_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_436_: u8 = 0; let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_439_: u8 = 0; let mut v___x_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_443_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_444_: u8 = 0; let mut v_unused_445_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_v_427_) == 0 {
let mut v_a_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_430_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_431_: u8 = 0; let mut v_isSharedCheck_436_: u8 = 0; 
lean_dec(v___y_426_);
v_a_428_ = lean_ctor_get(v_v_427_, 0);
v_isSharedCheck_436_ = (!lean_is_exclusive(v_v_427_)) as u8;
if v_isSharedCheck_436_ == 0 {
v___x_430_ = v_v_427_;
v_isShared_431_ = v_isSharedCheck_436_;
state = 1; continue;
} else {
lean_inc(v_a_428_);
lean_dec(v_v_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
state = 1; continue;
}
} else {
let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_439_: u8 = 0; let mut v_isSharedCheck_444_: u8 = 0; 
v_isSharedCheck_444_ = (!lean_is_exclusive(v_v_427_)) as u8;
if v_isSharedCheck_444_ == 0 {
let mut v_unused_445_: *mut lean_object = core::ptr::null_mut(); 
v_unused_445_ = lean_ctor_get(v_v_427_, 0);
lean_dec(v_unused_445_);
v___x_438_ = v_v_427_;
v_isShared_439_ = v_isSharedCheck_444_;
state = 3; continue;
} else {
lean_dec(v_v_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_431_ == 0 {
v___x_433_ = v___x_430_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_435_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_435_;
state = 2; continue;
}
}
3 => {
if v_isShared_439_ == 0 {
lean_ctor_set(v___x_438_, 0, v___y_426_);
v___x_441_ = v___x_438_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_443_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___y_426_);
v___x_441_ = v_reuseFailAlloc_443_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__3(mut v_inst_446_: *mut lean_object, mut v_00_u03b1_447_: *mut lean_object, mut v_00_u03b2_448_: *mut lean_object, mut v___y_449_: *mut lean_object, mut v___y_450_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_451_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_452_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_453_: *mut lean_object = core::ptr::null_mut(); let mut v___f_454_: *mut lean_object = core::ptr::null_mut(); let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_451_ = lean_ctor_get(v_inst_446_, 0);
lean_inc_ref(v_toApplicative_451_);
v_toBind_452_ = lean_ctor_get(v_inst_446_, 1);
lean_inc(v_toBind_452_);
lean_dec_ref(v_inst_446_);
v_toPure_453_ = lean_ctor_get(v_toApplicative_451_, 1);
lean_inc(v_toPure_453_);
lean_dec_ref(v_toApplicative_451_);
v___f_454_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_454_, 0, v_toPure_453_);
lean_closure_set(v___f_454_, 1, v___y_449_);
v___x_455_ = lean_apply_4(v_toBind_452_, lean_box(0), lean_box(0), v___y_450_, v___f_454_);
return v___x_455_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__4(mut v_toPure_456_: *mut lean_object, mut v_a_457_: *mut lean_object, mut v_v_458_: *mut lean_object) -> *mut lean_object{
let mut v_a_459_: *mut lean_object = core::ptr::null_mut(); let mut v___x_461_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_462_: u8 = 0; let mut v___x_464_: *mut lean_object = core::ptr::null_mut(); let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_466_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_467_: u8 = 0; let mut v_a_468_: *mut lean_object = core::ptr::null_mut(); let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_471_: u8 = 0; let mut v___x_472_: *mut lean_object = core::ptr::null_mut(); let mut v___x_474_: *mut lean_object = core::ptr::null_mut(); let mut v___x_475_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_476_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_477_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_v_458_) == 0 {
let mut v_a_459_: *mut lean_object = core::ptr::null_mut(); let mut v___x_461_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_462_: u8 = 0; let mut v_isSharedCheck_467_: u8 = 0; 
lean_dec(v_a_457_);
v_a_459_ = lean_ctor_get(v_v_458_, 0);
v_isSharedCheck_467_ = (!lean_is_exclusive(v_v_458_)) as u8;
if v_isSharedCheck_467_ == 0 {
v___x_461_ = v_v_458_;
v_isShared_462_ = v_isSharedCheck_467_;
state = 1; continue;
} else {
lean_inc(v_a_459_);
lean_dec(v_v_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
state = 1; continue;
}
} else {
let mut v_a_468_: *mut lean_object = core::ptr::null_mut(); let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_471_: u8 = 0; let mut v_isSharedCheck_477_: u8 = 0; 
v_a_468_ = lean_ctor_get(v_v_458_, 0);
v_isSharedCheck_477_ = (!lean_is_exclusive(v_v_458_)) as u8;
if v_isSharedCheck_477_ == 0 {
v___x_470_ = v_v_458_;
v_isShared_471_ = v_isSharedCheck_477_;
state = 3; continue;
} else {
lean_inc(v_a_468_);
lean_dec(v_v_458_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_462_ == 0 {
v___x_464_ = v___x_461_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_466_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_466_;
state = 2; continue;
}
}
3 => {
v___x_472_ = lean_apply_1(v_a_457_, v_a_468_);
if v_isShared_471_ == 0 {
lean_ctor_set(v___x_470_, 0, v___x_472_);
v___x_474_ = v___x_470_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_476_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_476_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__5(mut v_toPure_478_: *mut lean_object, mut v_x_479_: *mut lean_object, mut v_toBind_480_: *mut lean_object, mut v_v_481_: *mut lean_object) -> *mut lean_object{
let mut v_a_482_: *mut lean_object = core::ptr::null_mut(); let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_485_: u8 = 0; let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_489_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_490_: u8 = 0; let mut v_a_491_: *mut lean_object = core::ptr::null_mut(); let mut v___f_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_v_481_) == 0 {
let mut v_a_482_: *mut lean_object = core::ptr::null_mut(); let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_485_: u8 = 0; let mut v_isSharedCheck_490_: u8 = 0; 
lean_dec(v_toBind_480_);
lean_dec(v_x_479_);
v_a_482_ = lean_ctor_get(v_v_481_, 0);
v_isSharedCheck_490_ = (!lean_is_exclusive(v_v_481_)) as u8;
if v_isSharedCheck_490_ == 0 {
v___x_484_ = v_v_481_;
v_isShared_485_ = v_isSharedCheck_490_;
state = 1; continue;
} else {
lean_inc(v_a_482_);
lean_dec(v_v_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
state = 1; continue;
}
} else {
let mut v_a_491_: *mut lean_object = core::ptr::null_mut(); let mut v___f_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); 
v_a_491_ = lean_ctor_get(v_v_481_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v_v_481_, 1);
v___f_492_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__4 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_492_, 0, v_toPure_478_);
lean_closure_set(v___f_492_, 1, v_a_491_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_apply_1(v_x_479_, v___x_493_);
v___x_495_ = lean_apply_4(v_toBind_480_, lean_box(0), lean_box(0), v___x_494_, v___f_492_);
return v___x_495_;
}
}
1 => {
if v_isShared_485_ == 0 {
v___x_487_ = v___x_484_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_489_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_489_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__6(mut v_inst_496_: *mut lean_object, mut v_00_u03b1_497_: *mut lean_object, mut v_00_u03b2_498_: *mut lean_object, mut v_f_499_: *mut lean_object, mut v_x_500_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_501_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_502_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_503_: *mut lean_object = core::ptr::null_mut(); let mut v___f_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_501_ = lean_ctor_get(v_inst_496_, 0);
lean_inc_ref(v_toApplicative_501_);
v_toBind_502_ = lean_ctor_get(v_inst_496_, 1);
lean_inc_n(v_toBind_502_, 2);
lean_dec_ref(v_inst_496_);
v_toPure_503_ = lean_ctor_get(v_toApplicative_501_, 1);
lean_inc(v_toPure_503_);
lean_dec_ref(v_toApplicative_501_);
v___f_504_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__5 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_504_, 0, v_toPure_503_);
lean_closure_set(v___f_504_, 1, v_x_500_);
lean_closure_set(v___f_504_, 2, v_toBind_502_);
v___x_505_ = lean_apply_4(v_toBind_502_, lean_box(0), lean_box(0), v_f_499_, v___f_504_);
return v___x_505_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__7(mut v_toPure_506_: *mut lean_object, mut v_v_507_: *mut lean_object, mut v_v_508_: *mut lean_object) -> *mut lean_object{
let mut v_a_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_512_: u8 = 0; let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); let mut v___x_515_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_516_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_517_: u8 = 0; let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_v_508_) == 0 {
let mut v_a_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_512_: u8 = 0; let mut v_isSharedCheck_517_: u8 = 0; 
lean_dec_ref(v_v_507_);
v_a_509_ = lean_ctor_get(v_v_508_, 0);
v_isSharedCheck_517_ = (!lean_is_exclusive(v_v_508_)) as u8;
if v_isSharedCheck_517_ == 0 {
v___x_511_ = v_v_508_;
v_isShared_512_ = v_isSharedCheck_517_;
state = 1; continue;
} else {
lean_inc(v_a_509_);
lean_dec(v_v_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_517_;
state = 1; continue;
}
} else {
let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_v_508_, 1);
v___x_518_ = lean_apply_2(v_toPure_506_, lean_box(0), v_v_507_);
return v___x_518_;
}
}
1 => {
if v_isShared_512_ == 0 {
v___x_514_ = v___x_511_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_516_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_516_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__8(mut v_toPure_519_: *mut lean_object, mut v_y_520_: *mut lean_object, mut v_toBind_521_: *mut lean_object, mut v_v_522_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_v_522_) == 0 {
let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_toBind_521_);
lean_dec(v_y_520_);
v___x_523_ = lean_apply_2(v_toPure_519_, lean_box(0), v_v_522_);
return v___x_523_;
} else {
let mut v___f_524_: *mut lean_object = core::ptr::null_mut(); let mut v___x_525_: *mut lean_object = core::ptr::null_mut(); let mut v___x_526_: *mut lean_object = core::ptr::null_mut(); let mut v___x_527_: *mut lean_object = core::ptr::null_mut(); 
v___f_524_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__7 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_524_, 0, v_toPure_519_);
lean_closure_set(v___f_524_, 1, v_v_522_);
v___x_525_ = lean_box(0);
v___x_526_ = lean_apply_1(v_y_520_, v___x_525_);
v___x_527_ = lean_apply_4(v_toBind_521_, lean_box(0), lean_box(0), v___x_526_, v___f_524_);
return v___x_527_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__9(mut v_inst_528_: *mut lean_object, mut v_00_u03b1_529_: *mut lean_object, mut v_00_u03b2_530_: *mut lean_object, mut v_x_531_: *mut lean_object, mut v_y_532_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_533_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_534_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_535_: *mut lean_object = core::ptr::null_mut(); let mut v___f_536_: *mut lean_object = core::ptr::null_mut(); let mut v___x_537_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_533_ = lean_ctor_get(v_inst_528_, 0);
lean_inc_ref(v_toApplicative_533_);
v_toBind_534_ = lean_ctor_get(v_inst_528_, 1);
lean_inc_n(v_toBind_534_, 2);
lean_dec_ref(v_inst_528_);
v_toPure_535_ = lean_ctor_get(v_toApplicative_533_, 1);
lean_inc(v_toPure_535_);
lean_dec_ref(v_toApplicative_533_);
v___f_536_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__8 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_536_, 0, v_toPure_535_);
lean_closure_set(v___f_536_, 1, v_y_532_);
lean_closure_set(v___f_536_, 2, v_toBind_534_);
v___x_537_ = lean_apply_4(v_toBind_534_, lean_box(0), lean_box(0), v_x_531_, v___f_536_);
return v___x_537_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__10(mut v_toPure_538_: *mut lean_object, mut v_y_539_: *mut lean_object, mut v_v_540_: *mut lean_object) -> *mut lean_object{
let mut v_a_541_: *mut lean_object = core::ptr::null_mut(); let mut v___x_543_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_544_: u8 = 0; let mut v___x_546_: *mut lean_object = core::ptr::null_mut(); let mut v___x_547_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_548_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_549_: u8 = 0; let mut v___x_550_: *mut lean_object = core::ptr::null_mut(); let mut v___x_551_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_v_540_) == 0 {
let mut v_a_541_: *mut lean_object = core::ptr::null_mut(); let mut v___x_543_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_544_: u8 = 0; let mut v_isSharedCheck_549_: u8 = 0; 
lean_dec(v_y_539_);
v_a_541_ = lean_ctor_get(v_v_540_, 0);
v_isSharedCheck_549_ = (!lean_is_exclusive(v_v_540_)) as u8;
if v_isSharedCheck_549_ == 0 {
v___x_543_ = v_v_540_;
v_isShared_544_ = v_isSharedCheck_549_;
state = 1; continue;
} else {
lean_inc(v_a_541_);
lean_dec(v_v_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
state = 1; continue;
}
} else {
let mut v___x_550_: *mut lean_object = core::ptr::null_mut(); let mut v___x_551_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_v_540_, 1);
lean_dec(v_toPure_538_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_apply_1(v_y_539_, v___x_550_);
return v___x_551_;
}
}
1 => {
if v_isShared_544_ == 0 {
v___x_546_ = v___x_543_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_548_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_548_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg___lam__11(mut v_inst_552_: *mut lean_object, mut v_00_u03b1_553_: *mut lean_object, mut v_00_u03b2_554_: *mut lean_object, mut v_x_555_: *mut lean_object, mut v_y_556_: *mut lean_object) -> *mut lean_object{
let mut v_toApplicative_557_: *mut lean_object = core::ptr::null_mut(); let mut v_toBind_558_: *mut lean_object = core::ptr::null_mut(); let mut v_toPure_559_: *mut lean_object = core::ptr::null_mut(); let mut v___f_560_: *mut lean_object = core::ptr::null_mut(); let mut v___x_561_: *mut lean_object = core::ptr::null_mut(); 
v_toApplicative_557_ = lean_ctor_get(v_inst_552_, 0);
lean_inc_ref(v_toApplicative_557_);
v_toBind_558_ = lean_ctor_get(v_inst_552_, 1);
lean_inc(v_toBind_558_);
lean_dec_ref(v_inst_552_);
v_toPure_559_ = lean_ctor_get(v_toApplicative_557_, 1);
lean_inc(v_toPure_559_);
lean_dec_ref(v_toApplicative_557_);
v___f_560_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__10 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_560_, 0, v_toPure_559_);
lean_closure_set(v___f_560_, 1, v_y_556_);
v___x_561_ = lean_apply_4(v_toBind_558_, lean_box(0), lean_box(0), v_x_555_, v___f_560_);
return v___x_561_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad___redArg(mut v_inst_562_: *mut lean_object) -> *mut lean_object{
let mut v___f_563_: *mut lean_object = core::ptr::null_mut(); let mut v___f_564_: *mut lean_object = core::ptr::null_mut(); let mut v___f_565_: *mut lean_object = core::ptr::null_mut(); let mut v___f_566_: *mut lean_object = core::ptr::null_mut(); let mut v___f_567_: *mut lean_object = core::ptr::null_mut(); let mut v___x_568_: *mut lean_object = core::ptr::null_mut(); let mut v___x_569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_570_: *mut lean_object = core::ptr::null_mut(); let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); let mut v___x_572_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref_n(v_inst_562_, 6);
v___f_563_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__1 as *mut core::ffi::c_void, 5, 1);
lean_closure_set(v___f_563_, 0, v_inst_562_);
v___f_564_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__3 as *mut core::ffi::c_void, 5, 1);
lean_closure_set(v___f_564_, 0, v_inst_562_);
v___f_565_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__6 as *mut core::ffi::c_void, 5, 1);
lean_closure_set(v___f_565_, 0, v_inst_562_);
v___f_566_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__9 as *mut core::ffi::c_void, 5, 1);
lean_closure_set(v___f_566_, 0, v_inst_562_);
v___f_567_ = lean_alloc_closure(l_ExceptT_x27_instMonad___redArg___lam__11 as *mut core::ffi::c_void, 5, 1);
lean_closure_set(v___f_567_, 0, v_inst_562_);
v___x_568_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_568_, 0, v___f_563_);
lean_ctor_set(v___x_568_, 1, v___f_564_);
v___x_569_ = lean_alloc_closure(l_ExceptT_x27_pure as *mut core::ffi::c_void, 5, 3);
lean_closure_set(v___x_569_, 0, lean_box(0));
lean_closure_set(v___x_569_, 1, v_inst_562_);
lean_closure_set(v___x_569_, 2, lean_box(0));
v___x_570_ = lean_alloc_ctor(0, 5, (0) as u32);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
lean_ctor_set(v___x_570_, 2, v___f_565_);
lean_ctor_set(v___x_570_, 3, v___f_566_);
lean_ctor_set(v___x_570_, 4, v___f_567_);
v___x_571_ = lean_alloc_closure(l_ExceptT_x27_bind as *mut core::ffi::c_void, 7, 3);
lean_closure_set(v___x_571_, 0, lean_box(0));
lean_closure_set(v___x_571_, 1, v_inst_562_);
lean_closure_set(v___x_571_, 2, lean_box(0));
v___x_572_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
return v___x_572_;
}
#[no_mangle] pub unsafe extern "C" fn l_ExceptT_x27_instMonad(mut v_m_573_: *mut lean_object, mut v_inst_574_: *mut lean_object, mut v_00_u03b5_575_: *mut lean_object) -> *mut lean_object{
let mut v___x_576_: *mut lean_object = core::ptr::null_mut(); 
v___x_576_ = l_ExceptT_x27_instMonad___redArg(v_inst_574_);
return v___x_576_;
}
#[no_mangle] pub unsafe extern "C" fn l_read(mut v_a_577_: *mut lean_object) -> *mut lean_object{
let mut v___x_578_: *mut lean_object = core::ptr::null_mut(); let mut v___x_579_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_ref(v_a_577_);
v___x_578_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_578_, 0, v_a_577_);
v___x_579_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_a_577_);
return v___x_579_;
}
#[no_mangle] pub unsafe extern "C" fn l_write___redArg(mut v_s_582_: *mut lean_object) -> *mut lean_object{
let mut v___x_583_: *mut lean_object = core::ptr::null_mut(); let mut v___x_584_: *mut lean_object = core::ptr::null_mut(); 
v___x_583_ = l_write___redArg___closed__0;
v___x_584_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_s_582_);
return v___x_584_;
}
#[no_mangle] pub unsafe extern "C" fn l_write(mut v_s_585_: *mut lean_object, mut v_a_586_: *mut lean_object) -> *mut lean_object{
let mut v___x_587_: *mut lean_object = core::ptr::null_mut(); let mut v___x_588_: *mut lean_object = core::ptr::null_mut(); 
v___x_587_ = l_write___redArg___closed__0;
v___x_588_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_s_585_);
return v___x_588_;
}
#[no_mangle] pub unsafe extern "C" fn l_write___boxed(mut v_s_589_: *mut lean_object, mut v_a_590_: *mut lean_object) -> *mut lean_object{
let mut v_res_591_: *mut lean_object = core::ptr::null_mut(); 
v_res_591_ = l_write(v_s_589_, v_a_590_);
lean_dec_ref(v_a_590_);
return v_res_591_;
}
#[no_mangle] pub unsafe extern "C" fn l_updt(mut v_f_592_: *mut lean_object, mut v_a_593_: *mut lean_object) -> *mut lean_object{
let mut v___x_594_: *mut lean_object = core::ptr::null_mut(); let mut v___x_595_: *mut lean_object = core::ptr::null_mut(); let mut v___x_596_: *mut lean_object = core::ptr::null_mut(); 
v___x_594_ = lean_apply_1(v_f_592_, v_a_593_);
v___x_595_ = l_write___redArg___closed__0;
v___x_596_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
return v___x_596_;
}
#[no_mangle] pub unsafe extern "C" fn l_error___redArg(mut v_e_597_: *mut lean_object, mut v_a_598_: *mut lean_object) -> *mut lean_object{
let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); let mut v___x_600_: *mut lean_object = core::ptr::null_mut(); 
v___x_599_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_599_, 0, v_e_597_);
v___x_600_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v_a_598_);
return v___x_600_;
}
#[no_mangle] pub unsafe extern "C" fn l_error(mut v_00_u03b1_601_: *mut lean_object, mut v_e_602_: *mut lean_object, mut v_a_603_: *mut lean_object) -> *mut lean_object{
let mut v___x_604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_605_: *mut lean_object = core::ptr::null_mut(); 
v___x_604_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_604_, 0, v_e_602_);
v___x_605_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_a_603_);
return v___x_605_;
}
#[no_mangle] pub unsafe extern "C" fn l_run___redArg(mut v_x_606_: *mut lean_object, mut v_s_607_: *mut lean_object) -> *mut lean_object{
let mut v___x_608_: *mut lean_object = core::ptr::null_mut(); 
v___x_608_ = lean_apply_1(v_x_606_, v_s_607_);
return v___x_608_;
}
#[no_mangle] pub unsafe extern "C" fn l_run(mut v_00_u03b1_609_: *mut lean_object, mut v_x_610_: *mut lean_object, mut v_s_611_: *mut lean_object) -> *mut lean_object{
let mut v___x_612_: *mut lean_object = core::ptr::null_mut(); 
v___x_612_ = lean_apply_1(v_x_610_, v_s_611_);
return v___x_612_;
}
#[no_mangle] pub unsafe extern "C" fn l_capacity(mut v_a_613_: *mut lean_object) -> *mut lean_object{
let mut v___x_614_: *mut lean_object = core::ptr::null_mut(); let mut v___x_615_: *mut lean_object = core::ptr::null_mut(); let mut v___x_616_: *mut lean_object = core::ptr::null_mut(); 
v___x_614_ = lean_array_get_size(v_a_613_);
v___x_615_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_a_613_);
return v___x_616_;
}
#[no_mangle] pub unsafe extern "C" fn l_findEntryAux(mut v_x_623_: *mut lean_object, mut v_x_624_: *mut lean_object, mut v_a_625_: *mut lean_object) -> *mut lean_object{
let mut v_zero_626_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_627_: u8 = 0; let mut v___x_628_: *mut lean_object = core::ptr::null_mut(); let mut v___x_629_: *mut lean_object = core::ptr::null_mut(); let mut v___x_630_: *mut lean_object = core::ptr::null_mut(); let mut v___x_631_: u8 = 0; let mut v___x_632_: *mut lean_object = core::ptr::null_mut(); let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); let mut v___x_634_: *mut lean_object = core::ptr::null_mut(); let mut v_find_635_: *mut lean_object = core::ptr::null_mut(); let mut v___x_636_: u8 = 0; let mut v_one_637_: *mut lean_object = core::ptr::null_mut(); let mut v_n_638_: *mut lean_object = core::ptr::null_mut(); let mut v___x_639_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_640_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_644_: u8 = 0; let mut v_a_645_: *mut lean_object = core::ptr::null_mut(); let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v___x_648_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_649_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_650_: u8 = 0; let mut v_unused_651_: *mut lean_object = core::ptr::null_mut(); let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_626_ = lean_unsigned_to_nat(0);
v_isZero_627_ = lean_nat_dec_eq(v_x_623_, v_zero_626_);
if v_isZero_627_ == 1 {
let mut v___x_628_: *mut lean_object = core::ptr::null_mut(); let mut v___x_629_: *mut lean_object = core::ptr::null_mut(); 
v___x_628_ = l_findEntryAux___closed__1;
v___x_629_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_a_625_);
return v___x_629_;
} else {
let mut v___x_630_: *mut lean_object = core::ptr::null_mut(); let mut v___x_631_: u8 = 0; 
v___x_630_ = lean_array_get_size(v_a_625_);
v___x_631_ = lean_nat_dec_lt(v_x_624_, v___x_630_);
if v___x_631_ == 0 {
let mut v___x_632_: *mut lean_object = core::ptr::null_mut(); let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); 
v___x_632_ = l_findEntryAux___closed__3;
v___x_633_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v_a_625_);
return v___x_633_;
} else {
let mut v___x_634_: *mut lean_object = core::ptr::null_mut(); let mut v_find_635_: *mut lean_object = core::ptr::null_mut(); let mut v___x_636_: u8 = 0; 
v___x_634_ = lean_array_fget_borrowed(v_a_625_, v_x_624_);
v_find_635_ = lean_ctor_get(v___x_634_, 0);
v___x_636_ = lean_nat_dec_eq(v_find_635_, v_x_624_);
if v___x_636_ == 0 {
let mut v_one_637_: *mut lean_object = core::ptr::null_mut(); let mut v_n_638_: *mut lean_object = core::ptr::null_mut(); let mut v___x_639_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_640_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_find_635_);
v_one_637_ = lean_unsigned_to_nat(1);
v_n_638_ = lean_nat_sub(v_x_623_, v_one_637_);
v___x_639_ = l_findEntryAux(v_n_638_, v_find_635_, v_a_625_);
lean_dec(v_find_635_);
lean_dec(v_n_638_);
v_fst_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_fst_640_);
if lean_obj_tag(v_fst_640_) == 0 {
lean_dec_ref_known(v_fst_640_, 1);
return v___x_639_;
} else {
let mut v_snd_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_644_: u8 = 0; let mut v_isSharedCheck_650_: u8 = 0; 
v_snd_641_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_650_ = (!lean_is_exclusive(v___x_639_)) as u8;
if v_isSharedCheck_650_ == 0 {
let mut v_unused_651_: *mut lean_object = core::ptr::null_mut(); 
v_unused_651_ = lean_ctor_get(v___x_639_, 0);
lean_dec(v_unused_651_);
v___x_643_ = v___x_639_;
v_isShared_644_ = v_isSharedCheck_650_;
state = 1; continue;
} else {
lean_inc(v_snd_641_);
lean_dec(v___x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_650_;
state = 1; continue;
}
}
} else {
let mut v___x_652_: *mut lean_object = core::ptr::null_mut(); let mut v___x_653_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_634_);
v___x_652_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_652_, 0, v___x_634_);
v___x_653_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_a_625_);
return v___x_653_;
}
}
}
}
1 => {
v_a_645_ = lean_ctor_get(v_fst_640_, 0);
lean_inc(v_a_645_);
v___x_646_ = lean_array_set(v_snd_641_, v_x_624_, v_a_645_);
if v_isShared_644_ == 0 {
lean_ctor_set(v___x_643_, 1, v___x_646_);
v___x_648_ = v___x_643_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_649_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_fst_640_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_findEntryAux___boxed(mut v_x_654_: *mut lean_object, mut v_x_655_: *mut lean_object, mut v_a_656_: *mut lean_object) -> *mut lean_object{
let mut v_res_657_: *mut lean_object = core::ptr::null_mut(); 
v_res_657_ = l_findEntryAux(v_x_654_, v_x_655_, v_a_656_);
lean_dec(v_x_655_);
lean_dec(v_x_654_);
return v_res_657_;
}
#[no_mangle] pub unsafe extern "C" fn l_findEntry(mut v_n_658_: *mut lean_object, mut v_a_659_: *mut lean_object) -> *mut lean_object{
let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_661_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_662_: *mut lean_object = core::ptr::null_mut(); let mut v_a_663_: *mut lean_object = core::ptr::null_mut(); let mut v___x_664_: *mut lean_object = core::ptr::null_mut(); 
v___x_660_ = l_capacity(v_a_659_);
v_fst_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_fst_661_);
v_snd_662_ = lean_ctor_get(v___x_660_, 1);
lean_inc(v_snd_662_);
lean_dec_ref(v___x_660_);
v_a_663_ = lean_ctor_get(v_fst_661_, 0);
lean_inc(v_a_663_);
lean_dec(v_fst_661_);
v___x_664_ = l_findEntryAux(v_a_663_, v_n_658_, v_snd_662_);
lean_dec(v_a_663_);
return v___x_664_;
}
#[no_mangle] pub unsafe extern "C" fn l_findEntry___boxed(mut v_n_665_: *mut lean_object, mut v_a_666_: *mut lean_object) -> *mut lean_object{
let mut v_res_667_: *mut lean_object = core::ptr::null_mut(); 
v_res_667_ = l_findEntry(v_n_665_, v_a_666_);
lean_dec(v_n_665_);
return v_res_667_;
}
#[no_mangle] pub unsafe extern "C" fn l_find(mut v_n_668_: *mut lean_object, mut v_a_669_: *mut lean_object) -> *mut lean_object{
let mut v___x_670_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_671_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_674_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_675_: u8 = 0; let mut v_a_676_: *mut lean_object = core::ptr::null_mut(); let mut v___x_678_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_679_: u8 = 0; let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_684_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_685_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_686_: u8 = 0; let mut v_isSharedCheck_687_: u8 = 0; let mut v_unused_688_: *mut lean_object = core::ptr::null_mut(); let mut v_a_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_692_: u8 = 0; let mut v_snd_693_: *mut lean_object = core::ptr::null_mut(); let mut v___x_695_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_696_: u8 = 0; let mut v_find_697_: *mut lean_object = core::ptr::null_mut(); let mut v___x_699_: *mut lean_object = core::ptr::null_mut(); let mut v___x_701_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_702_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_703_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_704_: u8 = 0; let mut v_unused_705_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_706_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_670_ = l_findEntry(v_n_668_, v_a_669_);
v_fst_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_fst_671_);
if lean_obj_tag(v_fst_671_) == 0 {
let mut v_snd_672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_674_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_675_: u8 = 0; let mut v_isSharedCheck_687_: u8 = 0; 
v_snd_672_ = lean_ctor_get(v___x_670_, 1);
v_isSharedCheck_687_ = (!lean_is_exclusive(v___x_670_)) as u8;
if v_isSharedCheck_687_ == 0 {
let mut v_unused_688_: *mut lean_object = core::ptr::null_mut(); 
v_unused_688_ = lean_ctor_get(v___x_670_, 0);
lean_dec(v_unused_688_);
v___x_674_ = v___x_670_;
v_isShared_675_ = v_isSharedCheck_687_;
state = 1; continue;
} else {
lean_inc(v_snd_672_);
lean_dec(v___x_670_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_687_;
state = 1; continue;
}
} else {
let mut v_a_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_692_: u8 = 0; let mut v_isSharedCheck_706_: u8 = 0; 
v_a_689_ = lean_ctor_get(v_fst_671_, 0);
v_isSharedCheck_706_ = (!lean_is_exclusive(v_fst_671_)) as u8;
if v_isSharedCheck_706_ == 0 {
v___x_691_ = v_fst_671_;
v_isShared_692_ = v_isSharedCheck_706_;
state = 5; continue;
} else {
lean_inc(v_a_689_);
lean_dec(v_fst_671_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_706_;
state = 5; continue;
}
}
}
1 => {
v_a_676_ = lean_ctor_get(v_fst_671_, 0);
v_isSharedCheck_686_ = (!lean_is_exclusive(v_fst_671_)) as u8;
if v_isSharedCheck_686_ == 0 {
v___x_678_ = v_fst_671_;
v_isShared_679_ = v_isSharedCheck_686_;
state = 2; continue;
} else {
lean_inc(v_a_676_);
lean_dec(v_fst_671_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_686_;
state = 2; continue;
}
}
5 => {
v_snd_693_ = lean_ctor_get(v___x_670_, 1);
v_isSharedCheck_704_ = (!lean_is_exclusive(v___x_670_)) as u8;
if v_isSharedCheck_704_ == 0 {
let mut v_unused_705_: *mut lean_object = core::ptr::null_mut(); 
v_unused_705_ = lean_ctor_get(v___x_670_, 0);
lean_dec(v_unused_705_);
v___x_695_ = v___x_670_;
v_isShared_696_ = v_isSharedCheck_704_;
state = 6; continue;
} else {
lean_inc(v_snd_693_);
lean_dec(v___x_670_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_704_;
state = 6; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_find___boxed(mut v_n_707_: *mut lean_object, mut v_a_708_: *mut lean_object) -> *mut lean_object{
let mut v_res_709_: *mut lean_object = core::ptr::null_mut(); 
v_res_709_ = l_find(v_n_707_, v_a_708_);
lean_dec(v_n_707_);
return v_res_709_;
}
#[no_mangle] pub unsafe extern "C" fn l_mk(mut v_a_710_: *mut lean_object) -> *mut lean_object{
let mut v___x_711_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_712_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_713_: *mut lean_object = core::ptr::null_mut(); let mut v___x_715_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_716_: u8 = 0; let mut v_a_717_: *mut lean_object = core::ptr::null_mut(); let mut v___x_718_: *mut lean_object = core::ptr::null_mut(); let mut v___x_719_: *mut lean_object = core::ptr::null_mut(); let mut v___x_720_: *mut lean_object = core::ptr::null_mut(); let mut v___x_722_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_723_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_724_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_711_ = l_capacity(v_a_710_);
v_fst_712_ = lean_ctor_get(v___x_711_, 0);
v_snd_713_ = lean_ctor_get(v___x_711_, 1);
v_isSharedCheck_724_ = (!lean_is_exclusive(v___x_711_)) as u8;
if v_isSharedCheck_724_ == 0 {
v___x_715_ = v___x_711_;
v_isShared_716_ = v_isSharedCheck_724_;
state = 1; continue;
} else {
lean_inc(v_snd_713_);
lean_inc(v_fst_712_);
lean_dec(v___x_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_724_;
state = 1; continue;
}
}
1 => {
v_a_717_ = lean_ctor_get(v_fst_712_, 0);
v___x_718_ = lean_unsigned_to_nat(1);
lean_inc(v_a_717_);
v___x_719_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_719_, 0, v_a_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_array_push(v_snd_713_, v___x_719_);
if v_isShared_716_ == 0 {
lean_ctor_set(v___x_715_, 1, v___x_720_);
v___x_722_ = v___x_715_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_723_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_fst_712_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_union(mut v_n_u2081_725_: *mut lean_object, mut v_n_u2082_726_: *mut lean_object, mut v_a_727_: *mut lean_object) -> *mut lean_object{
let mut v___x_728_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_729_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_730_: *mut lean_object = core::ptr::null_mut(); let mut v___x_732_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_733_: u8 = 0; let mut v_a_734_: *mut lean_object = core::ptr::null_mut(); let mut v___x_736_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_737_: u8 = 0; let mut v___x_739_: *mut lean_object = core::ptr::null_mut(); let mut v___x_741_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_742_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_743_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_744_: u8 = 0; let mut v_isSharedCheck_745_: u8 = 0; let mut v_unused_746_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_747_: *mut lean_object = core::ptr::null_mut(); let mut v_a_748_: *mut lean_object = core::ptr::null_mut(); let mut v___x_749_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_750_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_751_: *mut lean_object = core::ptr::null_mut(); let mut v___x_753_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_754_: u8 = 0; let mut v_a_755_: *mut lean_object = core::ptr::null_mut(); let mut v___x_757_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_758_: u8 = 0; let mut v___x_760_: *mut lean_object = core::ptr::null_mut(); let mut v___x_762_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_763_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_764_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_765_: u8 = 0; let mut v_isSharedCheck_766_: u8 = 0; let mut v_unused_767_: *mut lean_object = core::ptr::null_mut(); let mut v_a_768_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_769_: *mut lean_object = core::ptr::null_mut(); let mut v___x_771_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_772_: u8 = 0; let mut v_find_773_: *mut lean_object = core::ptr::null_mut(); let mut v_rank_774_: *mut lean_object = core::ptr::null_mut(); let mut v___x_776_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_777_: u8 = 0; let mut v_find_778_: *mut lean_object = core::ptr::null_mut(); let mut v_rank_779_: *mut lean_object = core::ptr::null_mut(); let mut v___x_781_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_782_: u8 = 0; let mut v___x_783_: u8 = 0; let mut v___y_785_: *mut lean_object = core::ptr::null_mut(); let mut v___x_786_: *mut lean_object = core::ptr::null_mut(); let mut v___x_788_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_789_: *mut lean_object = core::ptr::null_mut(); let mut v___x_790_: u8 = 0; let mut v___x_791_: u8 = 0; let mut v___x_792_: *mut lean_object = core::ptr::null_mut(); let mut v___x_794_: *mut lean_object = core::ptr::null_mut(); let mut v___x_795_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_796_: *mut lean_object = core::ptr::null_mut(); let mut v___x_797_: *mut lean_object = core::ptr::null_mut(); let mut v___x_799_: *mut lean_object = core::ptr::null_mut(); let mut v___x_800_: *mut lean_object = core::ptr::null_mut(); let mut v___x_801_: *mut lean_object = core::ptr::null_mut(); let mut v___x_802_: *mut lean_object = core::ptr::null_mut(); let mut v___x_804_: *mut lean_object = core::ptr::null_mut(); let mut v___x_805_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_806_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_807_: *mut lean_object = core::ptr::null_mut(); let mut v___x_808_: *mut lean_object = core::ptr::null_mut(); let mut v___x_810_: *mut lean_object = core::ptr::null_mut(); let mut v___x_811_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_812_: *mut lean_object = core::ptr::null_mut(); let mut v___x_813_: *mut lean_object = core::ptr::null_mut(); let mut v___x_815_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_816_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_817_: u8 = 0; let mut v_isSharedCheck_818_: u8 = 0; let mut v_isSharedCheck_819_: u8 = 0; let mut v_unused_820_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_728_ = l_findEntry(v_n_u2081_725_, v_a_727_);
v_fst_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_fst_729_);
if lean_obj_tag(v_fst_729_) == 0 {
let mut v_snd_730_: *mut lean_object = core::ptr::null_mut(); let mut v___x_732_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_733_: u8 = 0; let mut v_isSharedCheck_745_: u8 = 0; 
v_snd_730_ = lean_ctor_get(v___x_728_, 1);
v_isSharedCheck_745_ = (!lean_is_exclusive(v___x_728_)) as u8;
if v_isSharedCheck_745_ == 0 {
let mut v_unused_746_: *mut lean_object = core::ptr::null_mut(); 
v_unused_746_ = lean_ctor_get(v___x_728_, 0);
lean_dec(v_unused_746_);
v___x_732_ = v___x_728_;
v_isShared_733_ = v_isSharedCheck_745_;
state = 1; continue;
} else {
lean_inc(v_snd_730_);
lean_dec(v___x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_745_;
state = 1; continue;
}
} else {
let mut v_snd_747_: *mut lean_object = core::ptr::null_mut(); let mut v_a_748_: *mut lean_object = core::ptr::null_mut(); let mut v___x_749_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_750_: *mut lean_object = core::ptr::null_mut(); 
v_snd_747_ = lean_ctor_get(v___x_728_, 1);
lean_inc(v_snd_747_);
lean_dec_ref(v___x_728_);
v_a_748_ = lean_ctor_get(v_fst_729_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v_fst_729_, 1);
v___x_749_ = l_findEntry(v_n_u2082_726_, v_snd_747_);
v_fst_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_fst_750_);
if lean_obj_tag(v_fst_750_) == 0 {
let mut v_snd_751_: *mut lean_object = core::ptr::null_mut(); let mut v___x_753_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_754_: u8 = 0; let mut v_isSharedCheck_766_: u8 = 0; 
lean_dec(v_a_748_);
v_snd_751_ = lean_ctor_get(v___x_749_, 1);
v_isSharedCheck_766_ = (!lean_is_exclusive(v___x_749_)) as u8;
if v_isSharedCheck_766_ == 0 {
let mut v_unused_767_: *mut lean_object = core::ptr::null_mut(); 
v_unused_767_ = lean_ctor_get(v___x_749_, 0);
lean_dec(v_unused_767_);
v___x_753_ = v___x_749_;
v_isShared_754_ = v_isSharedCheck_766_;
state = 5; continue;
} else {
lean_inc(v_snd_751_);
lean_dec(v___x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_766_;
state = 5; continue;
}
} else {
let mut v_a_768_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_769_: *mut lean_object = core::ptr::null_mut(); let mut v___x_771_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_772_: u8 = 0; let mut v_isSharedCheck_819_: u8 = 0; 
v_a_768_ = lean_ctor_get(v_fst_750_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v_fst_750_, 1);
v_snd_769_ = lean_ctor_get(v___x_749_, 1);
v_isSharedCheck_819_ = (!lean_is_exclusive(v___x_749_)) as u8;
if v_isSharedCheck_819_ == 0 {
let mut v_unused_820_: *mut lean_object = core::ptr::null_mut(); 
v_unused_820_ = lean_ctor_get(v___x_749_, 0);
lean_dec(v_unused_820_);
v___x_771_ = v___x_749_;
v_isShared_772_ = v_isSharedCheck_819_;
state = 9; continue;
} else {
lean_inc(v_snd_769_);
lean_dec(v___x_749_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_819_;
state = 9; continue;
}
}
}
}
1 => {
v_a_734_ = lean_ctor_get(v_fst_729_, 0);
v_isSharedCheck_744_ = (!lean_is_exclusive(v_fst_729_)) as u8;
if v_isSharedCheck_744_ == 0 {
v___x_736_ = v_fst_729_;
v_isShared_737_ = v_isSharedCheck_744_;
state = 2; continue;
} else {
lean_inc(v_a_734_);
lean_dec(v_fst_729_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_744_;
state = 2; continue;
}
}
5 => {
v_a_755_ = lean_ctor_get(v_fst_750_, 0);
v_isSharedCheck_765_ = (!lean_is_exclusive(v_fst_750_)) as u8;
if v_isSharedCheck_765_ == 0 {
v___x_757_ = v_fst_750_;
v_isShared_758_ = v_isSharedCheck_765_;
state = 6; continue;
} else {
lean_inc(v_a_755_);
lean_dec(v_fst_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_765_;
state = 6; continue;
}
}
9 => {
v_find_773_ = lean_ctor_get(v_a_748_, 0);
v_rank_774_ = lean_ctor_get(v_a_748_, 1);
v_isSharedCheck_818_ = (!lean_is_exclusive(v_a_748_)) as u8;
if v_isSharedCheck_818_ == 0 {
v___x_776_ = v_a_748_;
v_isShared_777_ = v_isSharedCheck_818_;
state = 10; continue;
} else {
lean_inc(v_rank_774_);
lean_inc(v_find_773_);
lean_dec(v_a_748_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_818_;
state = 10; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_union___boxed(mut v_n_u2081_821_: *mut lean_object, mut v_n_u2082_822_: *mut lean_object, mut v_a_823_: *mut lean_object) -> *mut lean_object{
let mut v_res_824_: *mut lean_object = core::ptr::null_mut(); 
v_res_824_ = l_union(v_n_u2081_821_, v_n_u2082_822_, v_a_823_);
lean_dec(v_n_u2082_822_);
lean_dec(v_n_u2081_821_);
return v_res_824_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkNodes(mut v_x_825_: *mut lean_object, mut v_a_826_: *mut lean_object) -> *mut lean_object{
let mut v_zero_827_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_828_: u8 = 0; let mut v___x_829_: *mut lean_object = core::ptr::null_mut(); let mut v___x_830_: *mut lean_object = core::ptr::null_mut(); let mut v___x_831_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_832_: *mut lean_object = core::ptr::null_mut(); let mut v_one_833_: *mut lean_object = core::ptr::null_mut(); let mut v_n_834_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_827_ = lean_unsigned_to_nat(0);
v_isZero_828_ = lean_nat_dec_eq(v_x_825_, v_zero_827_);
if v_isZero_828_ == 1 {
let mut v___x_829_: *mut lean_object = core::ptr::null_mut(); let mut v___x_830_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_825_);
v___x_829_ = l_write___redArg___closed__0;
v___x_830_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v_a_826_);
return v___x_830_;
} else {
let mut v___x_831_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_832_: *mut lean_object = core::ptr::null_mut(); let mut v_one_833_: *mut lean_object = core::ptr::null_mut(); let mut v_n_834_: *mut lean_object = core::ptr::null_mut(); 
v___x_831_ = l_mk(v_a_826_);
v_snd_832_ = lean_ctor_get(v___x_831_, 1);
lean_inc(v_snd_832_);
lean_dec_ref(v___x_831_);
v_one_833_ = lean_unsigned_to_nat(1);
v_n_834_ = lean_nat_sub(v_x_825_, v_one_833_);
lean_dec(v_x_825_);
v_x_825_ = v_n_834_;
v_a_826_ = v_snd_832_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_checkEq(mut v_n_u2081_839_: *mut lean_object, mut v_n_u2082_840_: *mut lean_object, mut v_a_841_: *mut lean_object) -> *mut lean_object{
let mut v___x_842_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_843_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_844_: *mut lean_object = core::ptr::null_mut(); let mut v___x_846_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_847_: u8 = 0; let mut v_a_848_: *mut lean_object = core::ptr::null_mut(); let mut v___x_850_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_851_: u8 = 0; let mut v___x_853_: *mut lean_object = core::ptr::null_mut(); let mut v___x_855_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_856_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_857_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_858_: u8 = 0; let mut v_isSharedCheck_859_: u8 = 0; let mut v_unused_860_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_861_: *mut lean_object = core::ptr::null_mut(); let mut v_a_862_: *mut lean_object = core::ptr::null_mut(); let mut v___x_863_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_864_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_865_: *mut lean_object = core::ptr::null_mut(); let mut v___x_867_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_868_: u8 = 0; let mut v_a_869_: *mut lean_object = core::ptr::null_mut(); let mut v___x_871_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_872_: u8 = 0; let mut v___x_874_: *mut lean_object = core::ptr::null_mut(); let mut v___x_876_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_877_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_878_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_879_: u8 = 0; let mut v_isSharedCheck_880_: u8 = 0; let mut v_unused_881_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_882_: *mut lean_object = core::ptr::null_mut(); let mut v___x_884_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_885_: u8 = 0; let mut v_a_886_: *mut lean_object = core::ptr::null_mut(); let mut v___x_887_: u8 = 0; let mut v___x_888_: *mut lean_object = core::ptr::null_mut(); let mut v___x_890_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_891_: *mut lean_object = core::ptr::null_mut(); let mut v___x_892_: *mut lean_object = core::ptr::null_mut(); let mut v___x_894_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_895_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_896_: u8 = 0; let mut v_unused_897_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_842_ = l_find(v_n_u2081_839_, v_a_841_);
v_fst_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_fst_843_);
if lean_obj_tag(v_fst_843_) == 0 {
let mut v_snd_844_: *mut lean_object = core::ptr::null_mut(); let mut v___x_846_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_847_: u8 = 0; let mut v_isSharedCheck_859_: u8 = 0; 
v_snd_844_ = lean_ctor_get(v___x_842_, 1);
v_isSharedCheck_859_ = (!lean_is_exclusive(v___x_842_)) as u8;
if v_isSharedCheck_859_ == 0 {
let mut v_unused_860_: *mut lean_object = core::ptr::null_mut(); 
v_unused_860_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_860_);
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_859_;
state = 1; continue;
} else {
lean_inc(v_snd_844_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_859_;
state = 1; continue;
}
} else {
let mut v_snd_861_: *mut lean_object = core::ptr::null_mut(); let mut v_a_862_: *mut lean_object = core::ptr::null_mut(); let mut v___x_863_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_864_: *mut lean_object = core::ptr::null_mut(); 
v_snd_861_ = lean_ctor_get(v___x_842_, 1);
lean_inc(v_snd_861_);
lean_dec_ref(v___x_842_);
v_a_862_ = lean_ctor_get(v_fst_843_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v_fst_843_, 1);
v___x_863_ = l_find(v_n_u2082_840_, v_snd_861_);
v_fst_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_fst_864_);
if lean_obj_tag(v_fst_864_) == 0 {
let mut v_snd_865_: *mut lean_object = core::ptr::null_mut(); let mut v___x_867_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_868_: u8 = 0; let mut v_isSharedCheck_880_: u8 = 0; 
lean_dec(v_a_862_);
v_snd_865_ = lean_ctor_get(v___x_863_, 1);
v_isSharedCheck_880_ = (!lean_is_exclusive(v___x_863_)) as u8;
if v_isSharedCheck_880_ == 0 {
let mut v_unused_881_: *mut lean_object = core::ptr::null_mut(); 
v_unused_881_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_881_);
v___x_867_ = v___x_863_;
v_isShared_868_ = v_isSharedCheck_880_;
state = 5; continue;
} else {
lean_inc(v_snd_865_);
lean_dec(v___x_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_880_;
state = 5; continue;
}
} else {
let mut v_snd_882_: *mut lean_object = core::ptr::null_mut(); let mut v___x_884_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_885_: u8 = 0; let mut v_isSharedCheck_896_: u8 = 0; 
v_snd_882_ = lean_ctor_get(v___x_863_, 1);
v_isSharedCheck_896_ = (!lean_is_exclusive(v___x_863_)) as u8;
if v_isSharedCheck_896_ == 0 {
let mut v_unused_897_: *mut lean_object = core::ptr::null_mut(); 
v_unused_897_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_897_);
v___x_884_ = v___x_863_;
v_isShared_885_ = v_isSharedCheck_896_;
state = 9; continue;
} else {
lean_inc(v_snd_882_);
lean_dec(v___x_863_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_896_;
state = 9; continue;
}
}
}
}
1 => {
v_a_848_ = lean_ctor_get(v_fst_843_, 0);
v_isSharedCheck_858_ = (!lean_is_exclusive(v_fst_843_)) as u8;
if v_isSharedCheck_858_ == 0 {
v___x_850_ = v_fst_843_;
v_isShared_851_ = v_isSharedCheck_858_;
state = 2; continue;
} else {
lean_inc(v_a_848_);
lean_dec(v_fst_843_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
state = 2; continue;
}
}
5 => {
v_a_869_ = lean_ctor_get(v_fst_864_, 0);
v_isSharedCheck_879_ = (!lean_is_exclusive(v_fst_864_)) as u8;
if v_isSharedCheck_879_ == 0 {
v___x_871_ = v_fst_864_;
v_isShared_872_ = v_isSharedCheck_879_;
state = 6; continue;
} else {
lean_inc(v_a_869_);
lean_dec(v_fst_864_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_879_;
state = 6; continue;
}
}
9 => {
v_a_886_ = lean_ctor_get(v_fst_864_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v_fst_864_, 1);
v___x_887_ = lean_nat_dec_eq(v_a_862_, v_a_886_);
lean_dec(v_a_886_);
lean_dec(v_a_862_);
if v___x_887_ == 0 {
let mut v___x_888_: *mut lean_object = core::ptr::null_mut(); let mut v___x_890_: *mut lean_object = core::ptr::null_mut(); 
v___x_888_ = l_checkEq___closed__1;
if v_isShared_885_ == 0 {
lean_ctor_set(v___x_884_, 0, v___x_888_);
v___x_890_ = v___x_884_;
state = 10; continue;
} else {
let mut v_reuseFailAlloc_891_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_snd_882_);
v___x_890_ = v_reuseFailAlloc_891_;
state = 10; continue;
}
} else {
let mut v___x_892_: *mut lean_object = core::ptr::null_mut(); let mut v___x_894_: *mut lean_object = core::ptr::null_mut(); 
v___x_892_ = l_write___redArg___closed__0;
if v_isShared_885_ == 0 {
lean_ctor_set(v___x_884_, 0, v___x_892_);
v___x_894_ = v___x_884_;
state = 11; continue;
} else {
let mut v_reuseFailAlloc_895_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_snd_882_);
v___x_894_ = v_reuseFailAlloc_895_;
state = 11; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_checkEq___boxed(mut v_n_u2081_898_: *mut lean_object, mut v_n_u2082_899_: *mut lean_object, mut v_a_900_: *mut lean_object) -> *mut lean_object{
let mut v_res_901_: *mut lean_object = core::ptr::null_mut(); 
v_res_901_ = l_checkEq(v_n_u2081_898_, v_n_u2082_899_, v_a_900_);
lean_dec(v_n_u2082_899_);
lean_dec(v_n_u2081_898_);
return v_res_901_;
}
#[no_mangle] pub unsafe extern "C" fn l_mergePackAux(mut v_x_902_: *mut lean_object, mut v_x_903_: *mut lean_object, mut v_x_904_: *mut lean_object, mut v_a_905_: *mut lean_object) -> *mut lean_object{
let mut v_zero_906_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_907_: u8 = 0; let mut v___x_908_: *mut lean_object = core::ptr::null_mut(); let mut v___x_909_: *mut lean_object = core::ptr::null_mut(); let mut v___x_910_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_911_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_912_: *mut lean_object = core::ptr::null_mut(); let mut v___x_914_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_915_: u8 = 0; let mut v_a_916_: *mut lean_object = core::ptr::null_mut(); let mut v___x_917_: *mut lean_object = core::ptr::null_mut(); let mut v___x_918_: u8 = 0; let mut v___x_919_: *mut lean_object = core::ptr::null_mut(); let mut v___x_921_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_922_: *mut lean_object = core::ptr::null_mut(); let mut v___x_923_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_924_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_925_: *mut lean_object = core::ptr::null_mut(); let mut v_one_926_: *mut lean_object = core::ptr::null_mut(); let mut v_n_927_: *mut lean_object = core::ptr::null_mut(); let mut v___x_928_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_930_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_zero_906_ = lean_unsigned_to_nat(0);
v_isZero_907_ = lean_nat_dec_eq(v_x_902_, v_zero_906_);
if v_isZero_907_ == 1 {
let mut v___x_908_: *mut lean_object = core::ptr::null_mut(); let mut v___x_909_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_903_);
lean_dec(v_x_902_);
v___x_908_ = l_write___redArg___closed__0;
v___x_909_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v_a_905_);
return v___x_909_;
} else {
let mut v___x_910_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_911_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_912_: *mut lean_object = core::ptr::null_mut(); let mut v___x_914_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_915_: u8 = 0; let mut v_isSharedCheck_930_: u8 = 0; 
v___x_910_ = l_capacity(v_a_905_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
v_snd_912_ = lean_ctor_get(v___x_910_, 1);
v_isSharedCheck_930_ = (!lean_is_exclusive(v___x_910_)) as u8;
if v_isSharedCheck_930_ == 0 {
v___x_914_ = v___x_910_;
v_isShared_915_ = v_isSharedCheck_930_;
state = 1; continue;
} else {
lean_inc(v_snd_912_);
lean_inc(v_fst_911_);
lean_dec(v___x_910_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_930_;
state = 1; continue;
}
}
}
1 => {
v_a_916_ = lean_ctor_get(v_fst_911_, 0);
lean_inc(v_a_916_);
lean_dec(v_fst_911_);
v___x_917_ = lean_nat_add(v_x_903_, v_x_904_);
v___x_918_ = lean_nat_dec_lt(v___x_917_, v_a_916_);
lean_dec(v_a_916_);
if v___x_918_ == 0 {
let mut v___x_919_: *mut lean_object = core::ptr::null_mut(); let mut v___x_921_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v___x_917_);
lean_dec(v_x_903_);
lean_dec(v_x_902_);
v___x_919_ = l_write___redArg___closed__0;
if v_isShared_915_ == 0 {
lean_ctor_set(v___x_914_, 0, v___x_919_);
v___x_921_ = v___x_914_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_922_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_snd_912_);
v___x_921_ = v_reuseFailAlloc_922_;
state = 2; continue;
}
} else {
let mut v___x_923_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_924_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_914_);
v___x_923_ = l_union(v_x_903_, v___x_917_, v_snd_912_);
lean_dec(v___x_917_);
v_fst_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_fst_924_);
if lean_obj_tag(v_fst_924_) == 0 {
lean_dec_ref_known(v_fst_924_, 1);
lean_dec(v_x_903_);
lean_dec(v_x_902_);
return v___x_923_;
} else {
let mut v_snd_925_: *mut lean_object = core::ptr::null_mut(); let mut v_one_926_: *mut lean_object = core::ptr::null_mut(); let mut v_n_927_: *mut lean_object = core::ptr::null_mut(); let mut v___x_928_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_fst_924_, 1);
v_snd_925_ = lean_ctor_get(v___x_923_, 1);
lean_inc(v_snd_925_);
lean_dec_ref(v___x_923_);
v_one_926_ = lean_unsigned_to_nat(1);
v_n_927_ = lean_nat_sub(v_x_902_, v_one_926_);
lean_dec(v_x_902_);
v___x_928_ = lean_nat_add(v_x_903_, v_one_926_);
lean_dec(v_x_903_);
v_x_902_ = v_n_927_;
v_x_903_ = v___x_928_;
v_a_905_ = v_snd_925_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_mergePackAux___boxed(mut v_x_931_: *mut lean_object, mut v_x_932_: *mut lean_object, mut v_x_933_: *mut lean_object, mut v_a_934_: *mut lean_object) -> *mut lean_object{
let mut v_res_935_: *mut lean_object = core::ptr::null_mut(); 
v_res_935_ = l_mergePackAux(v_x_931_, v_x_932_, v_x_933_, v_a_934_);
lean_dec(v_x_933_);
return v_res_935_;
}
#[no_mangle] pub unsafe extern "C" fn l_mergePack(mut v_d_936_: *mut lean_object, mut v_a_937_: *mut lean_object) -> *mut lean_object{
let mut v___x_938_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_939_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_940_: *mut lean_object = core::ptr::null_mut(); let mut v_a_941_: *mut lean_object = core::ptr::null_mut(); let mut v___x_942_: *mut lean_object = core::ptr::null_mut(); let mut v___x_943_: *mut lean_object = core::ptr::null_mut(); 
v___x_938_ = l_capacity(v_a_937_);
v_fst_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_fst_939_);
v_snd_940_ = lean_ctor_get(v___x_938_, 1);
lean_inc(v_snd_940_);
lean_dec_ref(v___x_938_);
v_a_941_ = lean_ctor_get(v_fst_939_, 0);
lean_inc(v_a_941_);
lean_dec(v_fst_939_);
v___x_942_ = lean_unsigned_to_nat(0);
v___x_943_ = l_mergePackAux(v_a_941_, v___x_942_, v_d_936_, v_snd_940_);
return v___x_943_;
}
#[no_mangle] pub unsafe extern "C" fn l_mergePack___boxed(mut v_d_944_: *mut lean_object, mut v_a_945_: *mut lean_object) -> *mut lean_object{
let mut v_res_946_: *mut lean_object = core::ptr::null_mut(); 
v_res_946_ = l_mergePack(v_d_944_, v_a_945_);
lean_dec(v_d_944_);
return v_res_946_;
}
#[no_mangle] pub unsafe extern "C" fn l_numEqsAux(mut v_x_947_: *mut lean_object, mut v_x_948_: *mut lean_object, mut v_x_949_: *mut lean_object, mut v_a_950_: *mut lean_object) -> *mut lean_object{
let mut v_zero_951_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_952_: u8 = 0; let mut v___x_953_: *mut lean_object = core::ptr::null_mut(); let mut v___x_954_: *mut lean_object = core::ptr::null_mut(); let mut v___x_955_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_956_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_957_: *mut lean_object = core::ptr::null_mut(); let mut v___x_959_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_960_: u8 = 0; let mut v_a_961_: *mut lean_object = core::ptr::null_mut(); let mut v___x_963_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_964_: u8 = 0; let mut v___x_965_: u8 = 0; let mut v___x_967_: *mut lean_object = core::ptr::null_mut(); let mut v___x_969_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_970_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_971_: *mut lean_object = core::ptr::null_mut(); let mut v___x_972_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_973_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_974_: *mut lean_object = core::ptr::null_mut(); let mut v_a_975_: *mut lean_object = core::ptr::null_mut(); let mut v_one_976_: *mut lean_object = core::ptr::null_mut(); let mut v_n_977_: *mut lean_object = core::ptr::null_mut(); let mut v___x_978_: *mut lean_object = core::ptr::null_mut(); let mut v___x_979_: u8 = 0; let mut v___x_980_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_983_: u8 = 0; let mut v_isSharedCheck_984_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_zero_951_ = lean_unsigned_to_nat(0);
v_isZero_952_ = lean_nat_dec_eq(v_x_947_, v_zero_951_);
if v_isZero_952_ == 1 {
let mut v___x_953_: *mut lean_object = core::ptr::null_mut(); let mut v___x_954_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_948_);
lean_dec(v_x_947_);
v___x_953_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_953_, 0, v_x_949_);
v___x_954_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v_a_950_);
return v___x_954_;
} else {
let mut v___x_955_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_956_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_957_: *mut lean_object = core::ptr::null_mut(); let mut v___x_959_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_960_: u8 = 0; let mut v_isSharedCheck_984_: u8 = 0; 
v___x_955_ = l_capacity(v_a_950_);
v_fst_956_ = lean_ctor_get(v___x_955_, 0);
v_snd_957_ = lean_ctor_get(v___x_955_, 1);
v_isSharedCheck_984_ = (!lean_is_exclusive(v___x_955_)) as u8;
if v_isSharedCheck_984_ == 0 {
v___x_959_ = v___x_955_;
v_isShared_960_ = v_isSharedCheck_984_;
state = 1; continue;
} else {
lean_inc(v_snd_957_);
lean_inc(v_fst_956_);
lean_dec(v___x_955_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_984_;
state = 1; continue;
}
}
}
1 => {
v_a_961_ = lean_ctor_get(v_fst_956_, 0);
v_isSharedCheck_983_ = (!lean_is_exclusive(v_fst_956_)) as u8;
if v_isSharedCheck_983_ == 0 {
v___x_963_ = v_fst_956_;
v_isShared_964_ = v_isSharedCheck_983_;
state = 2; continue;
} else {
lean_inc(v_a_961_);
lean_dec(v_fst_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_983_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_numEqs(mut v_a_985_: *mut lean_object) -> *mut lean_object{
let mut v___x_986_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_987_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_988_: *mut lean_object = core::ptr::null_mut(); let mut v_a_989_: *mut lean_object = core::ptr::null_mut(); let mut v___x_990_: *mut lean_object = core::ptr::null_mut(); let mut v___x_991_: *mut lean_object = core::ptr::null_mut(); 
v___x_986_ = l_capacity(v_a_985_);
v_fst_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_fst_987_);
v_snd_988_ = lean_ctor_get(v___x_986_, 1);
lean_inc(v_snd_988_);
lean_dec_ref(v___x_986_);
v_a_989_ = lean_ctor_get(v_fst_987_, 0);
lean_inc(v_a_989_);
lean_dec(v_fst_987_);
v___x_990_ = lean_unsigned_to_nat(0);
v___x_991_ = l_numEqsAux(v_a_989_, v___x_990_, v___x_990_, v_snd_988_);
return v___x_991_;
}
#[no_mangle] pub unsafe extern "C" fn l_test(mut v_n_995_: *mut lean_object, mut v_a_996_: *mut lean_object) -> *mut lean_object{
let mut v___x_997_: *mut lean_object = core::ptr::null_mut(); let mut v___x_998_: u8 = 0; let mut v___x_999_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1000_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1001_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1003_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1004_: u8 = 0; let mut v_a_1005_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1007_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1008_: u8 = 0; let mut v___x_1010_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1012_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1013_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1014_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1015_: u8 = 0; let mut v_isSharedCheck_1016_: u8 = 0; let mut v_unused_1017_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1018_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1019_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1020_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1021_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1022_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1024_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1025_: u8 = 0; let mut v_a_1026_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1028_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1029_: u8 = 0; let mut v___x_1031_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1033_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1034_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1035_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1036_: u8 = 0; let mut v_isSharedCheck_1037_: u8 = 0; let mut v_unused_1038_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1039_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1040_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1041_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1042_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1043_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1045_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1046_: u8 = 0; let mut v_a_1047_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1049_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1050_: u8 = 0; let mut v___x_1052_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1054_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1055_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1056_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1057_: u8 = 0; let mut v_isSharedCheck_1058_: u8 = 0; let mut v_unused_1059_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1060_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1061_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1062_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1063_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1064_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1066_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1067_: u8 = 0; let mut v_a_1068_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1070_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1071_: u8 = 0; let mut v___x_1073_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1075_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1076_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1077_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1078_: u8 = 0; let mut v_isSharedCheck_1079_: u8 = 0; let mut v_unused_1080_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1081_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1082_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1083_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1084_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1085_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1087_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1088_: u8 = 0; let mut v_a_1089_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1091_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1092_: u8 = 0; let mut v___x_1094_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1096_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1097_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1098_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1099_: u8 = 0; let mut v_isSharedCheck_1100_: u8 = 0; let mut v_unused_1101_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_1102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1105_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_997_ = lean_unsigned_to_nat(2);
v___x_998_ = lean_nat_dec_lt(v_n_995_, v___x_997_);
if v___x_998_ == 0 {
let mut v___x_999_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1000_: *mut lean_object = core::ptr::null_mut(); 
v___x_999_ = l_mkNodes(v_n_995_, v_a_996_);
v_fst_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_fst_1000_);
if lean_obj_tag(v_fst_1000_) == 0 {
let mut v_snd_1001_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1003_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1004_: u8 = 0; let mut v_isSharedCheck_1016_: u8 = 0; 
v_snd_1001_ = lean_ctor_get(v___x_999_, 1);
v_isSharedCheck_1016_ = (!lean_is_exclusive(v___x_999_)) as u8;
if v_isSharedCheck_1016_ == 0 {
let mut v_unused_1017_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1017_ = lean_ctor_get(v___x_999_, 0);
lean_dec(v_unused_1017_);
v___x_1003_ = v___x_999_;
v_isShared_1004_ = v_isSharedCheck_1016_;
state = 1; continue;
} else {
lean_inc(v_snd_1001_);
lean_dec(v___x_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1016_;
state = 1; continue;
}
} else {
let mut v_snd_1018_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1019_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1020_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1021_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_fst_1000_, 1);
v_snd_1018_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_snd_1018_);
lean_dec_ref(v___x_999_);
v___x_1019_ = lean_unsigned_to_nat(50000);
v___x_1020_ = l_mergePack(v___x_1019_, v_snd_1018_);
v_fst_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_fst_1021_);
if lean_obj_tag(v_fst_1021_) == 0 {
let mut v_snd_1022_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1024_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1025_: u8 = 0; let mut v_isSharedCheck_1037_: u8 = 0; 
v_snd_1022_ = lean_ctor_get(v___x_1020_, 1);
v_isSharedCheck_1037_ = (!lean_is_exclusive(v___x_1020_)) as u8;
if v_isSharedCheck_1037_ == 0 {
let mut v_unused_1038_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1038_ = lean_ctor_get(v___x_1020_, 0);
lean_dec(v_unused_1038_);
v___x_1024_ = v___x_1020_;
v_isShared_1025_ = v_isSharedCheck_1037_;
state = 5; continue;
} else {
lean_inc(v_snd_1022_);
lean_dec(v___x_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1037_;
state = 5; continue;
}
} else {
let mut v_snd_1039_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1040_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1041_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1042_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_fst_1021_, 1);
v_snd_1039_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_snd_1039_);
lean_dec_ref(v___x_1020_);
v___x_1040_ = lean_unsigned_to_nat(10000);
v___x_1041_ = l_mergePack(v___x_1040_, v_snd_1039_);
v_fst_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_fst_1042_);
if lean_obj_tag(v_fst_1042_) == 0 {
let mut v_snd_1043_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1045_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1046_: u8 = 0; let mut v_isSharedCheck_1058_: u8 = 0; 
v_snd_1043_ = lean_ctor_get(v___x_1041_, 1);
v_isSharedCheck_1058_ = (!lean_is_exclusive(v___x_1041_)) as u8;
if v_isSharedCheck_1058_ == 0 {
let mut v_unused_1059_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1059_ = lean_ctor_get(v___x_1041_, 0);
lean_dec(v_unused_1059_);
v___x_1045_ = v___x_1041_;
v_isShared_1046_ = v_isSharedCheck_1058_;
state = 9; continue;
} else {
lean_inc(v_snd_1043_);
lean_dec(v___x_1041_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1058_;
state = 9; continue;
}
} else {
let mut v_snd_1060_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1061_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1062_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1063_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_fst_1042_, 1);
v_snd_1060_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_snd_1060_);
lean_dec_ref(v___x_1041_);
v___x_1061_ = lean_unsigned_to_nat(5000);
v___x_1062_ = l_mergePack(v___x_1061_, v_snd_1060_);
v_fst_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_fst_1063_);
if lean_obj_tag(v_fst_1063_) == 0 {
let mut v_snd_1064_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1066_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1067_: u8 = 0; let mut v_isSharedCheck_1079_: u8 = 0; 
v_snd_1064_ = lean_ctor_get(v___x_1062_, 1);
v_isSharedCheck_1079_ = (!lean_is_exclusive(v___x_1062_)) as u8;
if v_isSharedCheck_1079_ == 0 {
let mut v_unused_1080_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1080_ = lean_ctor_get(v___x_1062_, 0);
lean_dec(v_unused_1080_);
v___x_1066_ = v___x_1062_;
v_isShared_1067_ = v_isSharedCheck_1079_;
state = 13; continue;
} else {
lean_inc(v_snd_1064_);
lean_dec(v___x_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1079_;
state = 13; continue;
}
} else {
let mut v_snd_1081_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1082_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1083_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1084_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_fst_1063_, 1);
v_snd_1081_ = lean_ctor_get(v___x_1062_, 1);
lean_inc(v_snd_1081_);
lean_dec_ref(v___x_1062_);
v___x_1082_ = lean_unsigned_to_nat(1000);
v___x_1083_ = l_mergePack(v___x_1082_, v_snd_1081_);
v_fst_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_fst_1084_);
if lean_obj_tag(v_fst_1084_) == 0 {
let mut v_snd_1085_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1087_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1088_: u8 = 0; let mut v_isSharedCheck_1100_: u8 = 0; 
v_snd_1085_ = lean_ctor_get(v___x_1083_, 1);
v_isSharedCheck_1100_ = (!lean_is_exclusive(v___x_1083_)) as u8;
if v_isSharedCheck_1100_ == 0 {
let mut v_unused_1101_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1101_ = lean_ctor_get(v___x_1083_, 0);
lean_dec(v_unused_1101_);
v___x_1087_ = v___x_1083_;
v_isShared_1088_ = v_isSharedCheck_1100_;
state = 17; continue;
} else {
lean_inc(v_snd_1085_);
lean_dec(v___x_1083_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1100_;
state = 17; continue;
}
} else {
let mut v_snd_1102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1103_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_fst_1084_, 1);
v_snd_1102_ = lean_ctor_get(v___x_1083_, 1);
lean_inc(v_snd_1102_);
lean_dec_ref(v___x_1083_);
v___x_1103_ = l_numEqs(v_snd_1102_);
return v___x_1103_;
}
}
}
}
}
} else {
let mut v___x_1104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1105_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_n_995_);
v___x_1104_ = l_test___closed__1;
v___x_1105_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_a_996_);
return v___x_1105_;
}
}
1 => {
v_a_1005_ = lean_ctor_get(v_fst_1000_, 0);
v_isSharedCheck_1015_ = (!lean_is_exclusive(v_fst_1000_)) as u8;
if v_isSharedCheck_1015_ == 0 {
v___x_1007_ = v_fst_1000_;
v_isShared_1008_ = v_isSharedCheck_1015_;
state = 2; continue;
} else {
lean_inc(v_a_1005_);
lean_dec(v_fst_1000_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1015_;
state = 2; continue;
}
}
5 => {
v_a_1026_ = lean_ctor_get(v_fst_1021_, 0);
v_isSharedCheck_1036_ = (!lean_is_exclusive(v_fst_1021_)) as u8;
if v_isSharedCheck_1036_ == 0 {
v___x_1028_ = v_fst_1021_;
v_isShared_1029_ = v_isSharedCheck_1036_;
state = 6; continue;
} else {
lean_inc(v_a_1026_);
lean_dec(v_fst_1021_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1036_;
state = 6; continue;
}
}
9 => {
v_a_1047_ = lean_ctor_get(v_fst_1042_, 0);
v_isSharedCheck_1057_ = (!lean_is_exclusive(v_fst_1042_)) as u8;
if v_isSharedCheck_1057_ == 0 {
v___x_1049_ = v_fst_1042_;
v_isShared_1050_ = v_isSharedCheck_1057_;
state = 10; continue;
} else {
lean_inc(v_a_1047_);
lean_dec(v_fst_1042_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1057_;
state = 10; continue;
}
}
13 => {
v_a_1068_ = lean_ctor_get(v_fst_1063_, 0);
v_isSharedCheck_1078_ = (!lean_is_exclusive(v_fst_1063_)) as u8;
if v_isSharedCheck_1078_ == 0 {
v___x_1070_ = v_fst_1063_;
v_isShared_1071_ = v_isSharedCheck_1078_;
state = 14; continue;
} else {
lean_inc(v_a_1068_);
lean_dec(v_fst_1063_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1078_;
state = 14; continue;
}
}
17 => {
v_a_1089_ = lean_ctor_get(v_fst_1084_, 0);
v_isSharedCheck_1099_ = (!lean_is_exclusive(v_fst_1084_)) as u8;
if v_isSharedCheck_1099_ == 0 {
v___x_1091_ = v_fst_1084_;
v_isShared_1092_ = v_isSharedCheck_1099_;
state = 18; continue;
} else {
lean_inc(v_a_1089_);
lean_dec(v_fst_1084_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1099_;
state = 18; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_1106_: *mut lean_object) -> *mut lean_object{
let mut v___x_1108_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_1109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1110_: *mut lean_object = core::ptr::null_mut(); 
v___x_1108_ = lean_get_stdout();
v_putStr_1109_ = lean_ctor_get(v___x_1108_, 4);
lean_inc_ref(v_putStr_1109_);
lean_dec_ref(v___x_1108_);
v___x_1110_ = lean_apply_2(v_putStr_1109_, v_s_1106_, lean_box(0));
return v___x_1110_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_1111_: *mut lean_object, mut v_a_1112_: *mut lean_object) -> *mut lean_object{
let mut v_res_1113_: *mut lean_object = core::ptr::null_mut(); 
v_res_1113_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_1111_);
return v_res_1113_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_1114_: *mut lean_object) -> *mut lean_object{
let mut v___x_1116_: u32 = 0; let mut v___x_1117_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1118_: *mut lean_object = core::ptr::null_mut(); 
v___x_1116_ = 10;
v___x_1117_ = lean_string_push(v_s_1114_, v___x_1116_);
v___x_1118_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_1117_);
return v___x_1118_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_1119_: *mut lean_object, mut v_a_1120_: *mut lean_object) -> *mut lean_object{
let mut v_res_1121_: *mut lean_object = core::ptr::null_mut(); 
v_res_1121_ = l_IO_println___at___00main_spec__0(v_s_1119_);
return v_res_1121_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_1127_: u32 = 0; let mut v___x_1128_: *mut lean_object = core::ptr::null_mut(); 
v___x_1127_ = 1;
v___x_1128_ = lean_box_uint32(v___x_1127_);
return v___x_1128_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__2() -> *mut lean_object{
let mut v___x_1129_: u32 = 0; let mut v___x_1130_: *mut lean_object = core::ptr::null_mut(); 
v___x_1129_ = 0;
v___x_1130_ = lean_box_uint32(v___x_1129_);
return v___x_1130_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_1131_: *mut lean_object) -> *mut lean_object{
let mut v___x_1133_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1137_: *mut lean_object = core::ptr::null_mut(); let mut v_n_1138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1140_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_1141_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1147_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1148_: u8 = 0; let mut v___x_1149_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1151_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1152_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1153_: u8 = 0; let mut v_unused_1154_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1157_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1158_: u8 = 0; let mut v___x_1160_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1161_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1162_: u8 = 0; let mut v_a_1163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1169_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1170_: u8 = 0; let mut v___x_1171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1173_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1174_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1175_: u8 = 0; let mut v_unused_1176_: *mut lean_object = core::ptr::null_mut(); let mut v_a_1177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1179_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1180_: u8 = 0; let mut v___x_1182_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_1183_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_1184_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_1133_ = l_main___closed__0;
v___x_1134_ = l_List_head_x21___redArg(v___x_1133_, v_xs_1131_);
lean_dec(v_xs_1131_);
v___x_1135_ = lean_unsigned_to_nat(0);
v___x_1136_ = lean_string_utf8_byte_size(v___x_1134_);
v___x_1137_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_1137_, 0, v___x_1134_);
lean_ctor_set(v___x_1137_, 1, v___x_1135_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
v_n_1138_ = l_String_Slice_toNat_x21(v___x_1137_);
lean_dec_ref_known(v___x_1137_, 3);
v___x_1139_ = l_main___closed__1;
v___x_1140_ = l_test(v_n_1138_, v___x_1139_);
v_fst_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_fst_1141_);
lean_dec_ref(v___x_1140_);
if lean_obj_tag(v_fst_1141_) == 0 {
let mut v_a_1142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1145_: *mut lean_object = core::ptr::null_mut(); 
v_a_1142_ = lean_ctor_get(v_fst_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v_fst_1141_, 1);
v___x_1143_ = l_main___closed__2;
v___x_1144_ = lean_string_append(v___x_1143_, v_a_1142_);
lean_dec(v_a_1142_);
v___x_1145_ = l_IO_println___at___00main_spec__0(v___x_1144_);
if lean_obj_tag(v___x_1145_) == 0 {
let mut v___x_1147_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1148_: u8 = 0; let mut v_isSharedCheck_1153_: u8 = 0; 
v_isSharedCheck_1153_ = (!lean_is_exclusive(v___x_1145_)) as u8;
if v_isSharedCheck_1153_ == 0 {
let mut v_unused_1154_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1154_ = lean_ctor_get(v___x_1145_, 0);
lean_dec(v_unused_1154_);
v___x_1147_ = v___x_1145_;
v_isShared_1148_ = v_isSharedCheck_1153_;
state = 1; continue;
} else {
lean_dec(v___x_1145_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
state = 1; continue;
}
} else {
let mut v_a_1155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1157_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1158_: u8 = 0; let mut v_isSharedCheck_1162_: u8 = 0; 
v_a_1155_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1162_ = (!lean_is_exclusive(v___x_1145_)) as u8;
if v_isSharedCheck_1162_ == 0 {
v___x_1157_ = v___x_1145_;
v_isShared_1158_ = v_isSharedCheck_1162_;
state = 3; continue;
} else {
lean_inc(v_a_1155_);
lean_dec(v___x_1145_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
state = 3; continue;
}
}
} else {
let mut v_a_1163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1167_: *mut lean_object = core::ptr::null_mut(); 
v_a_1163_ = lean_ctor_get(v_fst_1141_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v_fst_1141_, 1);
v___x_1164_ = l_main___closed__3;
v___x_1165_ = l_Nat_reprFast(v_a_1163_);
v___x_1166_ = lean_string_append(v___x_1164_, v___x_1165_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = l_IO_println___at___00main_spec__0(v___x_1166_);
if lean_obj_tag(v___x_1167_) == 0 {
let mut v___x_1169_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1170_: u8 = 0; let mut v_isSharedCheck_1175_: u8 = 0; 
v_isSharedCheck_1175_ = (!lean_is_exclusive(v___x_1167_)) as u8;
if v_isSharedCheck_1175_ == 0 {
let mut v_unused_1176_: *mut lean_object = core::ptr::null_mut(); 
v_unused_1176_ = lean_ctor_get(v___x_1167_, 0);
lean_dec(v_unused_1176_);
v___x_1169_ = v___x_1167_;
v_isShared_1170_ = v_isSharedCheck_1175_;
state = 5; continue;
} else {
lean_dec(v___x_1167_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
state = 5; continue;
}
} else {
let mut v_a_1177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_1179_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_1180_: u8 = 0; let mut v_isSharedCheck_1184_: u8 = 0; 
v_a_1177_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1184_ = (!lean_is_exclusive(v___x_1167_)) as u8;
if v_isSharedCheck_1184_ == 0 {
v___x_1179_ = v___x_1167_;
v_isShared_1180_ = v_isSharedCheck_1184_;
state = 7; continue;
} else {
lean_inc(v_a_1177_);
lean_dec(v___x_1167_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
state = 7; continue;
}
}
}
}
1 => {
v___x_1149_ = l_main___boxed__const__1;
if v_isShared_1148_ == 0 {
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1151_ = v___x_1147_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_1152_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
state = 2; continue;
}
}
3 => {
if v_isShared_1158_ == 0 {
v___x_1160_ = v___x_1157_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_1161_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
state = 4; continue;
}
}
5 => {
v___x_1171_ = l_main___boxed__const__2;
if v_isShared_1170_ == 0 {
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1173_ = v___x_1169_;
state = 6; continue;
} else {
let mut v_reuseFailAlloc_1174_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
state = 6; continue;
}
}
7 => {
if v_isShared_1180_ == 0 {
v___x_1182_ = v___x_1179_;
state = 8; continue;
} else {
let mut v_reuseFailAlloc_1183_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
state = 8; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_1185_: *mut lean_object, mut v_a_1186_: *mut lean_object) -> *mut lean_object{
let mut v_res_1187_: *mut lean_object = core::ptr::null_mut(); 
v_res_1187_ = _lean_main(v_xs_1185_);
return v_res_1187_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_unionfind(builtin: u8) -> *mut lean_object {
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
  let res = initialize_unionfind(1 /* builtin */);
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
