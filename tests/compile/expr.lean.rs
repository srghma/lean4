// Lean compiler output
// Module: expr
// Imports: public import Init public meta import Init public import Lean
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Lean_Expr_sort___override(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Name_mkStr1(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Expr_const___override(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_mkAppN(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Expr_getAppNumArgs(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_mk_array(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_expr_dbg_to_string(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Expr_hash(_: *mut lean_object) -> u64;
    fn lean_uint64_to_nat(_: u64) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_to_list(_: *mut lean_object) -> *mut lean_object;
    fn l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_resolveGlobalConstNoOverload___at___00__private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__1_spec__6(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_IO_println___at___00main_spec__1___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l_IO_println___at___00main_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [102, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object,1707590486618227741 as *mut lean_object] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__3_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__4_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object,7839396180116328695 as *mut lean_object] };
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__6_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [98, 0]};
static mut l_main___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__7_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 8) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object,10300200614825825839 as *mut lean_object] };
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
static mut l_main___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__8: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__9: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__10: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__11_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [104, 97, 115, 104, 58, 32, 0]};
static mut l_main___closed__11: *mut lean_object = core::ptr::addr_of!(l_main___closed__11_value) as *mut lean_object;
static mut l_main___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__12: u64 = 0;
static mut l_main___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__13: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__14: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__15_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__15: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__16_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__16: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__17: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__18_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__18: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__19_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__19: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__20_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__20: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_2_: *mut lean_object) -> *mut lean_object{
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: u32 = 0; let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = l_IO_println___at___00main_spec__1___closed__0;
v___x_5_ = lean_array_to_list(v_s_2_);
v___x_6_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_resolveGlobalConstNoOverload___at___00__private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__1_spec__6(v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lean_string_append(v___x_4_, v___x_6_);
lean_dec_ref(v___x_6_);
v___x_8_ = 10;
v___x_9_ = lean_string_push(v___x_7_, v___x_8_);
v___x_10_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_9_);
return v___x_10_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_11_: *mut lean_object, mut v_a_12_: *mut lean_object) -> *mut lean_object{
let mut v_res_13_: *mut lean_object = core::ptr::null_mut(); 
v_res_13_ = l_IO_println___at___00main_spec__1(v_s_11_);
return v_res_13_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_14_: *mut lean_object) -> *mut lean_object{
let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: u32 = 0; let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); 
v___x_16_ = lean_expr_dbg_to_string(v_s_14_);
v___x_17_ = 10;
v___x_18_ = lean_string_push(v___x_16_, v___x_17_);
v___x_19_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_18_);
return v___x_19_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_20_: *mut lean_object, mut v_a_21_: *mut lean_object) -> *mut lean_object{
let mut v_res_22_: *mut lean_object = core::ptr::null_mut(); 
v_res_22_ = l_IO_println___at___00main_spec__0(v_s_20_);
lean_dec_ref(v_s_20_);
return v_res_22_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
v___x_26_ = lean_box(0);
v___x_27_ = l_main___closed__1;
v___x_28_ = l_Lean_Expr_const___override(v___x_27_, v___x_26_);
return v___x_28_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
v___x_32_ = lean_box(0);
v___x_33_ = l_main___closed__4;
v___x_34_ = l_Lean_Expr_const___override(v___x_33_, v___x_32_);
return v___x_34_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_38_ = lean_box(0);
v___x_39_ = l_main___closed__7;
v___x_40_ = l_Lean_Expr_const___override(v___x_39_, v___x_38_);
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9() -> *mut lean_object{
let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); 
v___x_41_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_42_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_43_ = lean_unsigned_to_nat(2);
v___x_44_ = lean_mk_empty_array_with_capacity(v___x_43_);
v___x_45_ = lean_array_push(v___x_44_, v___x_42_);
v___x_46_ = lean_array_push(v___x_45_, v___x_41_);
return v___x_46_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> *mut lean_object{
let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v_e_49_: *mut lean_object = core::ptr::null_mut(); 
v___x_47_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_48_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v_e_49_ = l_Lean_mkAppN(v___x_48_, v___x_47_);
return v_e_49_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__12() -> u64{
let mut v_e_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: u64 = 0; 
v_e_51_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_52_ = l_Lean_Expr_hash(v_e_51_);
return v___x_52_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__13() -> *mut lean_object{
let mut v___x_53_: u64 = 0; let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); 
v___x_53_ = lean_uint64_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_54_ = lean_uint64_to_nat(v___x_53_);
return v___x_54_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__14() -> *mut lean_object{
let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); 
v___x_55_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__13), core::ptr::addr_of_mut!(l_main___closed__13_once), _init_l_main___closed__13);
v___x_56_ = l_Nat_reprFast(v___x_55_);
return v___x_56_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__15() -> *mut lean_object{
let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); 
v___x_57_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__14), core::ptr::addr_of_mut!(l_main___closed__14_once), _init_l_main___closed__14);
v___x_58_ = l_main___closed__11;
v___x_59_ = lean_string_append(v___x_58_, v___x_57_);
return v___x_59_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__16() -> *mut lean_object{
let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v_dummy_61_: *mut lean_object = core::ptr::null_mut(); 
v___x_60_ = lean_box(0);
v_dummy_61_ = l_Lean_Expr_sort___override(v___x_60_);
return v_dummy_61_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__17() -> *mut lean_object{
let mut v_e_62_: *mut lean_object = core::ptr::null_mut(); let mut v_nargs_63_: *mut lean_object = core::ptr::null_mut(); 
v_e_62_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v_nargs_63_ = l_Lean_Expr_getAppNumArgs(v_e_62_);
return v_nargs_63_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__18() -> *mut lean_object{
let mut v_dummy_64_: *mut lean_object = core::ptr::null_mut(); let mut v_nargs_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); 
v_dummy_64_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
v_nargs_65_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_66_ = lean_mk_array(v_nargs_65_, v_dummy_64_);
return v___x_66_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__19() -> *mut lean_object{
let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v_nargs_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); 
v___x_67_ = lean_unsigned_to_nat(1);
v_nargs_68_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_69_ = lean_nat_sub(v_nargs_68_, v___x_67_);
return v___x_69_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__20() -> *mut lean_object{
let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v_e_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); 
v___x_70_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__19), core::ptr::addr_of_mut!(l_main___closed__19_once), _init_l_main___closed__19);
v___x_71_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__18), core::ptr::addr_of_mut!(l_main___closed__18_once), _init_l_main___closed__18);
v_e_72_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_73_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_72_, v___x_71_, v___x_70_);
return v___x_73_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_74_: u32 = 0; let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); 
v___x_74_ = 0;
v___x_75_ = lean_box_uint32(v___x_74_);
return v___x_75_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v_e_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_85_: u8 = 0; let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_89_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_90_: u8 = 0; let mut v_unused_91_: *mut lean_object = core::ptr::null_mut(); let mut v_a_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_95_: u8 = 0; let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_98_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_99_: u8 = 0; let mut v_a_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_103_: u8 = 0; let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_106_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_107_: u8 = 0; let mut v_a_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_111_: u8 = 0; let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_114_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_115_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_e_77_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_78_ = l_IO_println___at___00main_spec__0(v_e_77_);
if lean_obj_tag(v___x_78_) == 0 {
let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_78_, 1);
v___x_79_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__15), core::ptr::addr_of_mut!(l_main___closed__15_once), _init_l_main___closed__15);
v___x_80_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_79_);
if lean_obj_tag(v___x_80_) == 0 {
let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_80_, 1);
v___x_81_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__20), core::ptr::addr_of_mut!(l_main___closed__20_once), _init_l_main___closed__20);
v___x_82_ = l_IO_println___at___00main_spec__1(v___x_81_);
if lean_obj_tag(v___x_82_) == 0 {
let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_85_: u8 = 0; let mut v_isSharedCheck_90_: u8 = 0; 
v_isSharedCheck_90_ = (!lean_is_exclusive(v___x_82_)) as u8;
if v_isSharedCheck_90_ == 0 {
let mut v_unused_91_: *mut lean_object = core::ptr::null_mut(); 
v_unused_91_ = lean_ctor_get(v___x_82_, 0);
lean_dec(v_unused_91_);
v___x_84_ = v___x_82_;
v_isShared_85_ = v_isSharedCheck_90_;
state = 1; continue;
} else {
lean_dec(v___x_82_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
state = 1; continue;
}
} else {
let mut v_a_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_95_: u8 = 0; let mut v_isSharedCheck_99_: u8 = 0; 
v_a_92_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_99_ = (!lean_is_exclusive(v___x_82_)) as u8;
if v_isSharedCheck_99_ == 0 {
v___x_94_ = v___x_82_;
v_isShared_95_ = v_isSharedCheck_99_;
state = 3; continue;
} else {
lean_inc(v_a_92_);
lean_dec(v___x_82_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
state = 3; continue;
}
}
} else {
let mut v_a_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_103_: u8 = 0; let mut v_isSharedCheck_107_: u8 = 0; 
v_a_100_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_107_ = (!lean_is_exclusive(v___x_80_)) as u8;
if v_isSharedCheck_107_ == 0 {
v___x_102_ = v___x_80_;
v_isShared_103_ = v_isSharedCheck_107_;
state = 5; continue;
} else {
lean_inc(v_a_100_);
lean_dec(v___x_80_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
state = 5; continue;
}
}
} else {
let mut v_a_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_111_: u8 = 0; let mut v_isSharedCheck_115_: u8 = 0; 
v_a_108_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_115_ = (!lean_is_exclusive(v___x_78_)) as u8;
if v_isSharedCheck_115_ == 0 {
v___x_110_ = v___x_78_;
v_isShared_111_ = v_isSharedCheck_115_;
state = 7; continue;
} else {
lean_inc(v_a_108_);
lean_dec(v___x_78_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
state = 7; continue;
}
}
}
1 => {
v___x_86_ = l_main___boxed__const__1;
if v_isShared_85_ == 0 {
lean_ctor_set(v___x_84_, 0, v___x_86_);
v___x_88_ = v___x_84_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_89_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
state = 2; continue;
}
}
3 => {
if v_isShared_95_ == 0 {
v___x_97_ = v___x_94_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_98_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
state = 4; continue;
}
}
5 => {
if v_isShared_103_ == 0 {
v___x_105_ = v___x_102_;
state = 6; continue;
} else {
let mut v_reuseFailAlloc_106_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
state = 6; continue;
}
}
7 => {
if v_isShared_111_ == 0 {
v___x_113_ = v___x_110_;
state = 8; continue;
} else {
let mut v_reuseFailAlloc_114_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
state = 8; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_116_: *mut lean_object) -> *mut lean_object{
let mut v_res_117_: *mut lean_object = core::ptr::null_mut(); 
v_res_117_ = _lean_main();
return v_res_117_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_expr(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  let res = initialize_expr(1 /* builtin */);
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
