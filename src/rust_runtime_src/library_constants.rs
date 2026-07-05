/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

const LIBRARY_CONSTANT_PATHS: &[&[&str]] = &[
    &["absurd"],
    &["And"],
    &["And", "left"],
    &["And", "right"],
    &["And", "intro"],
    &["And", "rec"],
    &["And", "casesOn"],
    &["Array"],
    &["Array", "sz"],
    &["Array", "toList"],
    &["autoParam"],
    &["bit0"],
    &["bit1"],
    &["HasOfNat", "ofNat"],
    &["ByteArray"],
    &["ByteArray", "data"],
    &["Bool"],
    &["Bool", "false"],
    &["Bool", "true"],
    &["Bool", "casesOn"],
    &["cast"],
    &["Char"],
    &["congrArg"],
    &["Decidable"],
    &["Decidable", "isTrue"],
    &["Decidable", "isFalse"],
    &["Decidable", "decide"],
    &["Empty"],
    &["Empty", "rec"],
    &["Empty", "casesOn"],
    &["Exists"],
    &["Eq"],
    &["Eq", "casesOn"],
    &["Eq", "recOn"],
    &["Eq", "rec"],
    &["Eq", "ndrec"],
    &["Eq", "refl"],
    &["Eq", "subst"],
    &["Eq", "symm"],
    &["Eq", "trans"],
    &["Float"],
    &["Float32"],
    &["FloatArray"],
    &["FloatArray", "data"],
    &["False"],
    &["False", "rec"],
    &["False", "casesOn"],
    &["HasAdd", "add"],
    &["HasNeg", "neg"],
    &["HasOne", "one"],
    &["HasZero", "zero"],
    &["HEq"],
    &["HEq", "refl"],
    &["Iff"],
    &["Iff", "refl"],
    &["Int"],
    &["Int", "natAbs"],
    &["Int", "decLt"],
    &["Int", "ofNat"],
    &["inline"],
    &["IO"],
    &["ite"],
    &["lcProof"],
    &["lcUnreachable"],
    &["List"],
    &["MutQuot"],
    &["Nat"],
    &["Nat", "succ"],
    &["Nat", "zero"],
    &["Nat", "HasZero"],
    &["Nat", "HasOne"],
    &["Nat", "HasAdd"],
    &["Nat", "add"],
    &["Nat", "decEq"],
    &["Nat", "sub"],
    &["ne"],
    &["Not"],
    &["optParam"],
    &["Or"],
    &["panic"],
    &["PUnit"],
    &["PUnit", "unit"],
    &["PProd"],
    &["PProd", "mk"],
    &["PProd", "fst"],
    &["PProd", "snd"],
    &["propext"],
    &["Quot", "mk"],
    &["Quot", "lift"],
    &["sorryAx"],
    &["String"],
    &["String", "data"],
    &["Subsingleton", "elim"],
    &["Task"],
    &["Thunk"],
    &["Thunk", "mk"],
    &["Thunk", "get"],
    &["True"],
    &["True", "intro"],
    &["Unit"],
    &["Unit", "unit"],
    &["UInt8"],
    &["UInt16"],
    &["UInt32"],
    &["UInt64"],
    &["USize"],
];

static mut LIBRARY_CONSTANTS: [LeanName; LIBRARY_CONSTANT_PATHS.len()] = [LeanName {
    obj: ptr::null_mut(),
};
    LIBRARY_CONSTANT_PATHS.len()];

unsafe fn library_constant(index: usize) -> *const LeanName {
    core::ptr::addr_of!(LIBRARY_CONSTANTS)
        .cast::<LeanName>()
        .add(index)
}

macro_rules! library_constant_getter {
    ($name:ident, $symbol:literal, $index:literal) => {
        #[cfg_attr(feature = "export-runtime-ffi", export_name = $symbol)]
        pub extern "C" fn $name() -> *const LeanName {
            unsafe { library_constant($index) }
        }
    };
}

library_constant_getter!(get_absurd_name, "_ZN4lean15get_absurd_nameEv", 0);
library_constant_getter!(get_and_name, "_ZN4lean12get_and_nameEv", 1);
library_constant_getter!(get_and_left_name, "_ZN4lean17get_and_left_nameEv", 2);
library_constant_getter!(get_and_right_name, "_ZN4lean18get_and_right_nameEv", 3);
library_constant_getter!(get_and_intro_name, "_ZN4lean18get_and_intro_nameEv", 4);
library_constant_getter!(get_and_rec_name, "_ZN4lean16get_and_rec_nameEv", 5);
library_constant_getter!(
    get_and_cases_on_name,
    "_ZN4lean21get_and_cases_on_nameEv",
    6
);
library_constant_getter!(get_array_name, "_ZN4lean14get_array_nameEv", 7);
library_constant_getter!(get_array_sz_name, "_ZN4lean17get_array_sz_nameEv", 8);
library_constant_getter!(
    get_array_to_list_name,
    "_ZN4lean22get_array_to_list_nameEv",
    9
);
library_constant_getter!(get_auto_param_name, "_ZN4lean19get_auto_param_nameEv", 10);
library_constant_getter!(get_bit0_name, "_ZN4lean13get_bit0_nameEv", 11);
library_constant_getter!(get_bit1_name, "_ZN4lean13get_bit1_nameEv", 12);
library_constant_getter!(
    get_has_of_nat_of_nat_name,
    "_ZN4lean26get_has_of_nat_of_nat_nameEv",
    13
);
library_constant_getter!(get_byte_array_name, "_ZN4lean19get_byte_array_nameEv", 14);
library_constant_getter!(
    get_byte_array_data_name,
    "_ZN4lean24get_byte_array_data_nameEv",
    15
);
library_constant_getter!(get_bool_name, "_ZN4lean13get_bool_nameEv", 16);
library_constant_getter!(get_bool_false_name, "_ZN4lean19get_bool_false_nameEv", 17);
library_constant_getter!(get_bool_true_name, "_ZN4lean18get_bool_true_nameEv", 18);
library_constant_getter!(
    get_bool_cases_on_name,
    "_ZN4lean22get_bool_cases_on_nameEv",
    19
);
library_constant_getter!(get_cast_name, "_ZN4lean13get_cast_nameEv", 20);
library_constant_getter!(get_char_name, "_ZN4lean13get_char_nameEv", 21);
library_constant_getter!(get_congr_arg_name, "_ZN4lean18get_congr_arg_nameEv", 22);
library_constant_getter!(get_decidable_name, "_ZN4lean18get_decidable_nameEv", 23);
library_constant_getter!(
    get_decidable_is_true_name,
    "_ZN4lean26get_decidable_is_true_nameEv",
    24
);
library_constant_getter!(
    get_decidable_is_false_name,
    "_ZN4lean27get_decidable_is_false_nameEv",
    25
);
library_constant_getter!(
    get_decidable_decide_name,
    "_ZN4lean25get_decidable_decide_nameEv",
    26
);
library_constant_getter!(get_empty_name, "_ZN4lean14get_empty_nameEv", 27);
library_constant_getter!(get_empty_rec_name, "_ZN4lean18get_empty_rec_nameEv", 28);
library_constant_getter!(
    get_empty_cases_on_name,
    "_ZN4lean23get_empty_cases_on_nameEv",
    29
);
library_constant_getter!(get_exists_name, "_ZN4lean15get_exists_nameEv", 30);
library_constant_getter!(get_eq_name, "_ZN4lean11get_eq_nameEv", 31);
library_constant_getter!(get_eq_cases_on_name, "_ZN4lean20get_eq_cases_on_nameEv", 32);
library_constant_getter!(get_eq_rec_on_name, "_ZN4lean18get_eq_rec_on_nameEv", 33);
library_constant_getter!(get_eq_rec_name, "_ZN4lean15get_eq_rec_nameEv", 34);
library_constant_getter!(get_eq_ndrec_name, "_ZN4lean17get_eq_ndrec_nameEv", 35);
library_constant_getter!(get_eq_refl_name, "_ZN4lean16get_eq_refl_nameEv", 36);
library_constant_getter!(get_eq_subst_name, "_ZN4lean17get_eq_subst_nameEv", 37);
library_constant_getter!(get_eq_symm_name, "_ZN4lean16get_eq_symm_nameEv", 38);
library_constant_getter!(get_eq_trans_name, "_ZN4lean17get_eq_trans_nameEv", 39);
library_constant_getter!(get_float_name, "_ZN4lean14get_float_nameEv", 40);
library_constant_getter!(get_float32_name, "_ZN4lean16get_float32_nameEv", 41);
library_constant_getter!(get_float_array_name, "_ZN4lean20get_float_array_nameEv", 42);
library_constant_getter!(
    get_float_array_data_name,
    "_ZN4lean25get_float_array_data_nameEv",
    43
);
library_constant_getter!(get_false_name, "_ZN4lean14get_false_nameEv", 44);
library_constant_getter!(get_false_rec_name, "_ZN4lean18get_false_rec_nameEv", 45);
library_constant_getter!(
    get_false_cases_on_name,
    "_ZN4lean23get_false_cases_on_nameEv",
    46
);
library_constant_getter!(get_has_add_add_name, "_ZN4lean20get_has_add_add_nameEv", 47);
library_constant_getter!(get_has_neg_neg_name, "_ZN4lean20get_has_neg_neg_nameEv", 48);
library_constant_getter!(get_has_one_one_name, "_ZN4lean20get_has_one_one_nameEv", 49);
library_constant_getter!(
    get_has_zero_zero_name,
    "_ZN4lean22get_has_zero_zero_nameEv",
    50
);
library_constant_getter!(get_heq_name, "_ZN4lean12get_heq_nameEv", 51);
library_constant_getter!(get_heq_refl_name, "_ZN4lean17get_heq_refl_nameEv", 52);
library_constant_getter!(get_iff_name, "_ZN4lean12get_iff_nameEv", 53);
library_constant_getter!(get_iff_refl_name, "_ZN4lean17get_iff_refl_nameEv", 54);
library_constant_getter!(get_int_name, "_ZN4lean12get_int_nameEv", 55);
library_constant_getter!(get_int_nat_abs_name, "_ZN4lean20get_int_nat_abs_nameEv", 56);
library_constant_getter!(get_int_dec_lt_name, "_ZN4lean19get_int_dec_lt_nameEv", 57);
library_constant_getter!(get_int_of_nat_name, "_ZN4lean19get_int_of_nat_nameEv", 58);
library_constant_getter!(get_inline_name, "_ZN4lean15get_inline_nameEv", 59);
library_constant_getter!(get_io_name, "_ZN4lean11get_io_nameEv", 60);
library_constant_getter!(get_ite_name, "_ZN4lean12get_ite_nameEv", 61);
library_constant_getter!(get_lc_proof_name, "_ZN4lean17get_lc_proof_nameEv", 62);
library_constant_getter!(
    get_lc_unreachable_name,
    "_ZN4lean23get_lc_unreachable_nameEv",
    63
);
library_constant_getter!(get_list_name, "_ZN4lean13get_list_nameEv", 64);
library_constant_getter!(get_mut_quot_name, "_ZN4lean17get_mut_quot_nameEv", 65);
library_constant_getter!(get_nat_name, "_ZN4lean12get_nat_nameEv", 66);
library_constant_getter!(get_nat_succ_name, "_ZN4lean17get_nat_succ_nameEv", 67);
library_constant_getter!(get_nat_zero_name, "_ZN4lean17get_nat_zero_nameEv", 68);
library_constant_getter!(
    get_nat_has_zero_name,
    "_ZN4lean21get_nat_has_zero_nameEv",
    69
);
library_constant_getter!(get_nat_has_one_name, "_ZN4lean20get_nat_has_one_nameEv", 70);
library_constant_getter!(get_nat_has_add_name, "_ZN4lean20get_nat_has_add_nameEv", 71);
library_constant_getter!(get_nat_add_name, "_ZN4lean16get_nat_add_nameEv", 72);
library_constant_getter!(get_nat_dec_eq_name, "_ZN4lean19get_nat_dec_eq_nameEv", 73);
library_constant_getter!(get_nat_sub_name, "_ZN4lean16get_nat_sub_nameEv", 74);
library_constant_getter!(get_ne_name, "_ZN4lean11get_ne_nameEv", 75);
library_constant_getter!(get_not_name, "_ZN4lean12get_not_nameEv", 76);
library_constant_getter!(get_opt_param_name, "_ZN4lean18get_opt_param_nameEv", 77);
library_constant_getter!(get_or_name, "_ZN4lean11get_or_nameEv", 78);
library_constant_getter!(get_panic_name, "_ZN4lean14get_panic_nameEv", 79);
library_constant_getter!(get_punit_name, "_ZN4lean14get_punit_nameEv", 80);
library_constant_getter!(get_punit_unit_name, "_ZN4lean19get_punit_unit_nameEv", 81);
library_constant_getter!(get_pprod_name, "_ZN4lean14get_pprod_nameEv", 82);
library_constant_getter!(get_pprod_mk_name, "_ZN4lean17get_pprod_mk_nameEv", 83);
library_constant_getter!(get_pprod_fst_name, "_ZN4lean18get_pprod_fst_nameEv", 84);
library_constant_getter!(get_pprod_snd_name, "_ZN4lean18get_pprod_snd_nameEv", 85);
library_constant_getter!(get_propext_name, "_ZN4lean16get_propext_nameEv", 86);
library_constant_getter!(get_quot_mk_name, "_ZN4lean16get_quot_mk_nameEv", 87);
library_constant_getter!(get_quot_lift_name, "_ZN4lean18get_quot_lift_nameEv", 88);
library_constant_getter!(get_sorry_ax_name, "_ZN4lean17get_sorry_ax_nameEv", 89);
library_constant_getter!(get_string_name, "_ZN4lean15get_string_nameEv", 90);
library_constant_getter!(get_string_data_name, "_ZN4lean20get_string_data_nameEv", 91);
library_constant_getter!(
    get_subsingleton_elim_name,
    "_ZN4lean26get_subsingleton_elim_nameEv",
    92
);
library_constant_getter!(get_task_name, "_ZN4lean13get_task_nameEv", 93);
library_constant_getter!(get_thunk_name, "_ZN4lean14get_thunk_nameEv", 94);
library_constant_getter!(get_thunk_mk_name, "_ZN4lean17get_thunk_mk_nameEv", 95);
library_constant_getter!(get_thunk_get_name, "_ZN4lean18get_thunk_get_nameEv", 96);
library_constant_getter!(get_true_name, "_ZN4lean13get_true_nameEv", 97);
library_constant_getter!(get_true_intro_name, "_ZN4lean19get_true_intro_nameEv", 98);
library_constant_getter!(get_unit_name, "_ZN4lean13get_unit_nameEv", 99);
library_constant_getter!(get_unit_unit_name, "_ZN4lean18get_unit_unit_nameEv", 100);
library_constant_getter!(get_uint8_name, "_ZN4lean14get_uint8_nameEv", 101);
library_constant_getter!(get_uint16_name, "_ZN4lean15get_uint16_nameEv", 102);
library_constant_getter!(get_uint32_name, "_ZN4lean15get_uint32_nameEv", 103);
library_constant_getter!(get_uint64_name, "_ZN4lean15get_uint64_nameEv", 104);
library_constant_getter!(get_usize_name, "_ZN4lean14get_usize_nameEv", 105);

#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean20initialize_constantsEv"
)]
pub extern "C" fn initialize_constants() {
    unsafe {
        for (index, path) in LIBRARY_CONSTANT_PATHS.iter().enumerate() {
            let value = mk_name_path(path);
            lean_mark_persistent(value.obj);
            LIBRARY_CONSTANTS[index] = value;
        }
    }
}

#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean18finalize_constantsEv"
)]
pub extern "C" fn finalize_constants() {
    unsafe {
        for index in 0..LIBRARY_CONSTANT_PATHS.len() {
            let value = LIBRARY_CONSTANTS[index].obj;
            if !value.is_null() {
                lean_dec(value);
                LIBRARY_CONSTANTS[index].obj = ptr::null_mut();
            }
        }
    }
}
