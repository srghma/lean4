// Lean compiler output
// Module: ilean_roundtrip
// Imports: public import Init public meta import Init public import Lean.Data.Lsp
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Lean_Lsp_RefInfo_Location_mk(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_io_mono_ms_now() -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Json_mkObj(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Json_compress(_: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn l_List_get_x21Internal___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_byte_size(_: *mut lean_object) -> *mut lean_object;
    fn l_String_Slice_toNat_x21(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_float_of_nat(_: *mut lean_object) -> f64;
    fn l_Float_ofScientific(_: *mut lean_object, _: u8, _: *mut lean_object) -> f64;
    fn lean_float_div(_: f64, _: f64) -> f64;
    fn lean_float_to_string(_: f64) -> *mut lean_object;
    fn l_IO_println___at___00Lean_Environment_displayStats_spec__1(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Json_parse(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___closed__0_value: lean_string_object<30> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [65, 46, 82, 101, 97, 115, 111, 110, 97, 98, 108, 121, 46, 76, 111, 110, 103, 46, 77, 111, 100, 117, 108, 101, 46, 78, 97, 109, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___closed__1_value: lean_string_object<42> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [65, 46, 82, 101, 97, 115, 111, 110, 97, 98, 108, 121, 46, 76, 111, 110, 103, 46, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 78, 97, 109, 101, 46, 102, 111, 111, 98, 97, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [((( 333 as usize) << 1) | 1) as *mut lean_object,((( 444 as usize) << 1) | 1) as *mut lean_object] };
static mut l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__1_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [((( 444 as usize) << 1) | 1) as *mut lean_object,((( 555 as usize) << 1) | 1) as *mut lean_object] };
static mut l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__2_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__0_value) as *mut lean_object,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__1_value) as *mut lean_object] };
static mut l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__3_value: lean_string_object<41> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [65, 46, 82, 101, 97, 115, 111, 110, 97, 98, 108, 121, 46, 76, 111, 110, 103, 46, 80, 97, 114, 101, 110, 116, 68, 101, 99, 108, 46, 78, 97, 109, 101, 46, 98, 97, 114, 102, 111, 111, 0]};
static mut l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__3: *mut lean_object = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__4_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__3_value) as *mut lean_object] };
static mut l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__4: *mut lean_object = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__4_value) as *mut lean_object;
static mut l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_genModuleRefs___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_genModuleRefs___closed__0: *mut lean_object = core::ptr::addr_of!(l_genModuleRefs___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_genModuleRefs___closed__1_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 200 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_genModuleRefs___closed__1: *mut lean_object = core::ptr::addr_of!(l_genModuleRefs___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_genModuleRefs___closed__2_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_genModuleRefs___closed__1_value) as *mut lean_object] };
static mut l_genModuleRefs___closed__2: *mut lean_object = core::ptr::addr_of!(l_genModuleRefs___closed__2_value) as *mut lean_object;
static mut l_genModuleRefs___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_genModuleRefs___closed__3: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: f64 = 0.0;
#[no_mangle] pub static l_main___closed__2_value: lean_string_object<23> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [109, 101, 97, 115, 117, 114, 101, 109, 101, 110, 116, 58, 32, 99, 111, 109, 112, 114, 101, 115, 115, 32, 0]};
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 115, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__4_value: lean_string_object<20> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [109, 101, 97, 115, 117, 114, 101, 109, 101, 110, 116, 58, 32, 112, 97, 114, 115, 101, 32, 0]};
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__5_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 114, 114, 111, 114, 0]};
static mut l_main___closed__5: *mut lean_object = core::ptr::addr_of!(l_main___closed__5_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg(mut v_upperBound_3_: *mut lean_object, mut v___x_4_: *mut lean_object, mut v_a_5_: *mut lean_object, mut v_b_6_: *mut lean_object) -> *mut lean_object{
let mut v___x_8_: u8 = 0; let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_8_ = lean_nat_dec_lt(v_a_5_, v_upperBound_3_);
if v___x_8_ == 0 {
let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_a_5_);
lean_dec_ref(v___x_4_);
v___x_9_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_9_, 0, v_b_6_);
return v___x_9_;
} else {
let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); 
v___x_10_ = l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___closed__0;
lean_inc(v_a_5_);
v___x_11_ = l_Nat_reprFast(v_a_5_);
v___x_12_ = lean_string_append(v___x_10_, v___x_11_);
v___x_13_ = l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___closed__1;
v___x_14_ = lean_string_append(v___x_13_, v___x_11_);
lean_dec_ref(v___x_11_);
v___x_15_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_15_, 0, v___x_12_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
lean_inc_ref(v___x_4_);
v___x_16_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v___x_15_, v___x_4_, v_b_6_);
v___x_17_ = lean_unsigned_to_nat(1);
v___x_18_ = lean_nat_add(v_a_5_, v___x_17_);
lean_dec(v_a_5_);
v_a_5_ = v___x_18_;
v_b_6_ = v___x_16_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg___boxed(mut v_upperBound_20_: *mut lean_object, mut v___x_21_: *mut lean_object, mut v_a_22_: *mut lean_object, mut v_b_23_: *mut lean_object, mut v___y_24_: *mut lean_object) -> *mut lean_object{
let mut v_res_25_: *mut lean_object = core::ptr::null_mut(); 
v_res_25_ = l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg(v_upperBound_20_, v___x_21_, v_a_22_, v_b_23_);
lean_dec(v_upperBound_20_);
return v_res_25_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5() -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v_someLoc_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_38_ = l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__4;
v___x_39_ = l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__2;
v_someLoc_40_ = l_Lean_Lsp_RefInfo_Location_mk(v___x_39_, v___x_38_);
return v_someLoc_40_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg(mut v_as_x27_41_: *mut lean_object, mut v_b_42_: *mut lean_object) -> *mut lean_object{
let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_45_: *mut lean_object = core::ptr::null_mut(); let mut v_someLoc_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_as_x27_41_) == 0 {
let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
v___x_44_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_44_, 0, v_b_42_);
return v___x_44_;
} else {
let mut v_tail_45_: *mut lean_object = core::ptr::null_mut(); let mut v_someLoc_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); 
v_tail_45_ = lean_ctor_get(v_as_x27_41_, 1);
v_someLoc_46_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5);
v___x_47_ = lean_array_push(v_b_42_, v_someLoc_46_);
v_as_x27_41_ = v_tail_45_;
v_b_42_ = v___x_47_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___boxed(mut v_as_x27_49_: *mut lean_object, mut v_b_50_: *mut lean_object, mut v___y_51_: *mut lean_object) -> *mut lean_object{
let mut v_res_52_: *mut lean_object = core::ptr::null_mut(); 
v_res_52_ = l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg(v_as_x27_49_, v_b_50_);
lean_dec(v_as_x27_49_);
return v_res_52_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_genModuleRefs___closed__3() -> *mut lean_object{
let mut v_someLoc_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
v_someLoc_61_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg___closed__5);
v___x_62_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_62_, 0, v_someLoc_61_);
return v___x_62_;
}
#[no_mangle] pub unsafe extern "C" fn l_genModuleRefs(mut v_n_63_: *mut lean_object) -> *mut lean_object{
let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v_someUsages_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v_a_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); 
v___x_65_ = lean_unsigned_to_nat(0);
v_someUsages_66_ = l_genModuleRefs___closed__0;
v___x_67_ = l_genModuleRefs___closed__2;
v___x_68_ = l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg(v___x_67_, v_someUsages_66_);
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
lean_dec_ref(v___x_68_);
v___x_70_ = lean_box(1);
v___x_71_ = lean_obj_once(core::ptr::addr_of_mut!(l_genModuleRefs___closed__3), core::ptr::addr_of_mut!(l_genModuleRefs___closed__3_once), _init_l_genModuleRefs___closed__3);
v___x_72_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_a_69_);
v___x_73_ = l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg(v_n_63_, v___x_72_, v___x_65_, v___x_70_);
return v___x_73_;
}
#[no_mangle] pub unsafe extern "C" fn l_genModuleRefs___boxed(mut v_n_74_: *mut lean_object, mut v_a_75_: *mut lean_object) -> *mut lean_object{
let mut v_res_76_: *mut lean_object = core::ptr::null_mut(); 
v_res_76_ = l_genModuleRefs(v_n_74_);
lean_dec(v_n_74_);
return v_res_76_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00genModuleRefs_spec__0(mut v_as_77_: *mut lean_object, mut v_as_x27_78_: *mut lean_object, mut v_b_79_: *mut lean_object, mut v_a_80_: *mut lean_object) -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___redArg(v_as_x27_78_, v_b_79_);
return v___x_82_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_forIn_x27_loop___at___00genModuleRefs_spec__0___boxed(mut v_as_83_: *mut lean_object, mut v_as_x27_84_: *mut lean_object, mut v_b_85_: *mut lean_object, mut v_a_86_: *mut lean_object, mut v___y_87_: *mut lean_object) -> *mut lean_object{
let mut v_res_88_: *mut lean_object = core::ptr::null_mut(); 
v_res_88_ = l_List_forIn_x27_loop___at___00genModuleRefs_spec__0(v_as_83_, v_as_x27_84_, v_b_85_, v_a_86_);
lean_dec(v_as_x27_84_);
lean_dec(v_as_83_);
return v_res_88_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1(mut v_upperBound_89_: *mut lean_object, mut v___x_90_: *mut lean_object, mut v_inst_91_: *mut lean_object, mut v_R_92_: *mut lean_object, mut v_a_93_: *mut lean_object, mut v_b_94_: *mut lean_object, mut v_c_95_: *mut lean_object) -> *mut lean_object{
let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); 
v___x_97_ = l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___redArg(v_upperBound_89_, v___x_90_, v_a_93_, v_b_94_);
return v___x_97_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1___boxed(mut v_upperBound_98_: *mut lean_object, mut v___x_99_: *mut lean_object, mut v_inst_100_: *mut lean_object, mut v_R_101_: *mut lean_object, mut v_a_102_: *mut lean_object, mut v_b_103_: *mut lean_object, mut v_c_104_: *mut lean_object, mut v___y_105_: *mut lean_object) -> *mut lean_object{
let mut v_res_106_: *mut lean_object = core::ptr::null_mut(); 
v_res_106_ = l_WellFounded_opaqueFix_u2083___at___00genModuleRefs_spec__1(v_upperBound_98_, v___x_99_, v_inst_100_, v_R_101_, v_a_102_, v_b_103_, v_c_104_);
lean_dec(v_upperBound_98_);
return v_res_106_;
}
#[no_mangle] pub unsafe extern "C" fn l_compress(mut v_refs_107_: *mut lean_object) -> *mut lean_object{
let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); 
v___x_109_ = lean_box(0);
v___x_110_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_109_, v_refs_107_);
v___x_111_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_110_, v___x_109_);
v___x_112_ = l_Lean_Json_mkObj(v___x_111_);
lean_dec(v___x_111_);
v___x_113_ = l_Lean_Json_compress(v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
#[no_mangle] pub unsafe extern "C" fn l_compress___boxed(mut v_refs_115_: *mut lean_object, mut v_a_116_: *mut lean_object) -> *mut lean_object{
let mut v_res_117_: *mut lean_object = core::ptr::null_mut(); 
v_res_117_ = l_compress(v_refs_115_);
lean_dec(v_refs_115_);
return v_res_117_;
}
#[no_mangle] pub unsafe extern "C" fn l_parse(mut v_s_118_: *mut lean_object) -> *mut lean_object{
let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); 
v___x_120_ = l_Lean_Json_parse(v_s_118_);
v___x_121_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
#[no_mangle] pub unsafe extern "C" fn l_parse___boxed(mut v_s_122_: *mut lean_object, mut v_a_123_: *mut lean_object) -> *mut lean_object{
let mut v_res_124_: *mut lean_object = core::ptr::null_mut(); 
v_res_124_ = l_parse(v_s_122_);
return v_res_124_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0() -> *mut lean_object{
let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); 
v___x_126_ = lean_io_mono_ms_now();
v___x_127_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0___boxed(mut v___y_128_: *mut lean_object) -> *mut lean_object{
let mut v_res_129_: *mut lean_object = core::ptr::null_mut(); 
v_res_129_ = l_main___lam__0();
return v_res_129_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> f64{
let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: u8 = 0; let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v___x_134_: f64 = 0.0; 
v___x_131_ = lean_unsigned_to_nat(1);
v___x_132_ = 1;
v___x_133_ = lean_unsigned_to_nat(10000);
v___x_134_ = l_Float_ofScientific(v___x_133_, v___x_132_, v___x_131_);
return v___x_134_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_args_139_: *mut lean_object) -> *mut lean_object{
let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); let mut v_n_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v_a_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_a_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v_a_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v_a_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: f64 = 0.0; let mut v___x_157_: f64 = 0.0; let mut v___x_158_: f64 = 0.0; let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v_a_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v_a_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: f64 = 0.0; let mut v___x_172_: f64 = 0.0; let mut v___x_173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v_a_185_: *mut lean_object = core::ptr::null_mut(); let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_188_: u8 = 0; let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_191_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_192_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_141_ = l_main___closed__0;
v___x_142_ = lean_unsigned_to_nat(0);
v___x_143_ = l_List_get_x21Internal___redArg(v___x_141_, v_args_139_, v___x_142_);
lean_dec(v_args_139_);
v___x_144_ = lean_string_utf8_byte_size(v___x_143_);
v___x_145_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v___x_142_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
v_n_146_ = l_String_Slice_toNat_x21(v___x_145_);
lean_dec_ref_known(v___x_145_, 3);
v___x_147_ = l_genModuleRefs(v_n_146_);
lean_dec(v_n_146_);
if lean_obj_tag(v___x_147_) == 0 {
let mut v_a_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_a_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v_a_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v_a_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: f64 = 0.0; let mut v___x_157_: f64 = 0.0; let mut v___x_158_: f64 = 0.0; let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = l_main___lam__0();
v_a_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_a_150_);
lean_dec_ref(v___x_149_);
v___x_151_ = l_compress(v_a_148_);
lean_dec(v_a_148_);
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref(v___x_151_);
v___x_153_ = l_main___lam__0();
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref(v___x_153_);
v___x_155_ = lean_nat_sub(v_a_154_, v_a_150_);
lean_dec(v_a_150_);
lean_dec(v_a_154_);
v___x_156_ = lean_float_of_nat(v___x_155_);
v___x_157_ = lean_float_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_158_ = lean_float_div(v___x_156_, v___x_157_);
v___x_159_ = l_main___closed__2;
v___x_160_ = lean_float_to_string(v___x_158_);
v___x_161_ = lean_string_append(v___x_159_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = l_main___closed__3;
v___x_163_ = lean_string_append(v___x_161_, v___x_162_);
v___x_164_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_163_);
if lean_obj_tag(v___x_164_) == 0 {
let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v_a_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v_a_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: f64 = 0.0; let mut v___x_172_: f64 = 0.0; 
lean_dec_ref_known(v___x_164_, 1);
v___x_165_ = l_main___lam__0();
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_parse(v_a_152_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref(v___x_167_);
v___x_169_ = lean_io_mono_ms_now();
v___x_170_ = lean_nat_sub(v___x_169_, v_a_166_);
lean_dec(v_a_166_);
lean_dec(v___x_169_);
v___x_171_ = lean_float_of_nat(v___x_170_);
v___x_172_ = lean_float_div(v___x_171_, v___x_157_);
if lean_obj_tag(v_a_168_) == 0 {
let mut v___x_173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_a_168_, 1);
v___x_173_ = l_main___closed__4;
v___x_174_ = lean_float_to_string(v___x_172_);
v___x_175_ = lean_string_append(v___x_173_, v___x_174_);
lean_dec_ref(v___x_174_);
v___x_176_ = lean_string_append(v___x_175_, v___x_162_);
v___x_177_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_176_);
if lean_obj_tag(v___x_177_) == 0 {
let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_177_, 1);
v___x_178_ = l_main___closed__5;
v___x_179_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_178_);
return v___x_179_;
} else {
return v___x_177_;
}
} else {
let mut v___x_180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_183_: *mut lean_object = core::ptr::null_mut(); let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_a_168_, 1);
v___x_180_ = l_main___closed__4;
v___x_181_ = lean_float_to_string(v___x_172_);
v___x_182_ = lean_string_append(v___x_180_, v___x_181_);
lean_dec_ref(v___x_181_);
v___x_183_ = lean_string_append(v___x_182_, v___x_162_);
v___x_184_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_183_);
return v___x_184_;
}
} else {
lean_dec(v_a_152_);
return v___x_164_;
}
} else {
let mut v_a_185_: *mut lean_object = core::ptr::null_mut(); let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_188_: u8 = 0; let mut v_isSharedCheck_192_: u8 = 0; 
v_a_185_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_192_ = (!lean_is_exclusive(v___x_147_)) as u8;
if v_isSharedCheck_192_ == 0 {
v___x_187_ = v___x_147_;
v_isShared_188_ = v_isSharedCheck_192_;
state = 1; continue;
} else {
lean_inc(v_a_185_);
lean_dec(v___x_147_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
state = 1; continue;
}
}
}
1 => {
if v_isShared_188_ == 0 {
v___x_190_ = v___x_187_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_191_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_args_193_: *mut lean_object, mut v_a_194_: *mut lean_object) -> *mut lean_object{
let mut v_res_195_: *mut lean_object = core::ptr::null_mut(); 
v_res_195_ = _lean_main(v_args_193_);
return v_res_195_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_Lsp(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_ilean__roundtrip(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
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
  let res = initialize_ilean__roundtrip(1 /* builtin */);
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
