use std::ptr;

use leanh_l1::emitted::lean_mark_persistent::lean_mark_persistent;

use crate::r#priv::{initialize_constructions_module::LeanName, mk_name_path::mk_name_path};

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
    ($name:ident, $index:literal) => {
        pub fn $name() -> *const LeanName {
            unsafe { library_constant($index) }
        }
    };
}

library_constant_getter!(get_absurd_name, 0);
library_constant_getter!(get_and_name, 1);
library_constant_getter!(get_and_left_name, 2);
library_constant_getter!(get_and_right_name, 3);
library_constant_getter!(get_and_intro_name, 4);
library_constant_getter!(get_and_rec_name, 5);
library_constant_getter!(get_and_cases_on_name, 6);
library_constant_getter!(get_array_name, 7);
library_constant_getter!(get_array_sz_name, 8);
library_constant_getter!(get_array_to_list_name, 9);
library_constant_getter!(get_auto_param_name, 10);
library_constant_getter!(get_bit0_name, 11);
library_constant_getter!(get_bit1_name, 12);
library_constant_getter!(get_has_of_nat_of_nat_name, 13);
library_constant_getter!(get_byte_array_name, 14);
library_constant_getter!(get_byte_array_data_name, 15);
library_constant_getter!(get_bool_name, 16);
library_constant_getter!(get_bool_false_name, 17);
library_constant_getter!(get_bool_true_name, 18);
library_constant_getter!(get_bool_cases_on_name, 19);
library_constant_getter!(get_cast_name, 20);
library_constant_getter!(get_char_name, 21);
library_constant_getter!(get_congr_arg_name, 22);
library_constant_getter!(get_decidable_name, 23);
library_constant_getter!(get_decidable_is_true_name, 24);
library_constant_getter!(get_decidable_is_false_name, 25);
library_constant_getter!(get_decidable_decide_name, 26);
library_constant_getter!(get_empty_name, 27);
library_constant_getter!(get_empty_rec_name, 28);
library_constant_getter!(get_empty_cases_on_name, 29);
library_constant_getter!(get_exists_name, 30);
library_constant_getter!(get_eq_name, 31);
library_constant_getter!(get_eq_cases_on_name, 32);
library_constant_getter!(get_eq_rec_on_name, 33);
library_constant_getter!(get_eq_rec_name, 34);
library_constant_getter!(get_eq_ndrec_name, 35);
library_constant_getter!(get_eq_refl_name, 36);
library_constant_getter!(get_eq_subst_name, 37);
library_constant_getter!(get_eq_symm_name, 38);
library_constant_getter!(get_eq_trans_name, 39);
library_constant_getter!(get_float_name, 40);
library_constant_getter!(get_float32_name, 41);
library_constant_getter!(get_float_array_name, 42);
library_constant_getter!(get_float_array_data_name, 43);
library_constant_getter!(get_false_name, 44);
library_constant_getter!(get_false_rec_name, 45);
library_constant_getter!(get_false_cases_on_name, 46);
library_constant_getter!(get_has_add_add_name, 47);
library_constant_getter!(get_has_neg_neg_name, 48);
library_constant_getter!(get_has_one_one_name, 49);
library_constant_getter!(get_has_zero_zero_name, 50);
library_constant_getter!(get_heq_name, 51);
library_constant_getter!(get_heq_refl_name, 52);
library_constant_getter!(get_iff_name, 53);
library_constant_getter!(get_iff_refl_name, 54);
library_constant_getter!(get_int_name, 55);
library_constant_getter!(get_int_nat_abs_name, 56);
library_constant_getter!(get_int_dec_lt_name, 57);
library_constant_getter!(get_int_of_nat_name, 58);
library_constant_getter!(get_inline_name, 59);
library_constant_getter!(get_io_name, 60);
library_constant_getter!(get_ite_name, 61);
library_constant_getter!(get_lc_proof_name, 62);
library_constant_getter!(get_lc_unreachable_name, 63);
library_constant_getter!(get_list_name, 64);
library_constant_getter!(get_mut_quot_name, 65);
library_constant_getter!(get_nat_name, 66);
library_constant_getter!(get_nat_succ_name, 67);
library_constant_getter!(get_nat_zero_name, 68);
library_constant_getter!(get_nat_has_zero_name, 69);
library_constant_getter!(get_nat_has_one_name, 70);
library_constant_getter!(get_nat_has_add_name, 71);
library_constant_getter!(get_nat_add_name, 72);
library_constant_getter!(get_nat_dec_eq_name, 73);
library_constant_getter!(get_nat_sub_name, 74);
library_constant_getter!(get_ne_name, 75);
library_constant_getter!(get_not_name, 76);
library_constant_getter!(get_opt_param_name, 77);
library_constant_getter!(get_or_name, 78);
library_constant_getter!(get_panic_name, 79);
library_constant_getter!(get_punit_name, 80);
library_constant_getter!(get_punit_unit_name, 81);
library_constant_getter!(get_pprod_name, 82);
library_constant_getter!(get_pprod_mk_name, 83);
library_constant_getter!(get_pprod_fst_name, 84);
library_constant_getter!(get_pprod_snd_name, 85);
library_constant_getter!(get_propext_name, 86);
library_constant_getter!(get_quot_mk_name, 87);
library_constant_getter!(get_quot_lift_name, 88);
library_constant_getter!(get_sorry_ax_name, 89);
library_constant_getter!(get_string_name, 90);
library_constant_getter!(get_string_data_name, 91);
library_constant_getter!(get_subsingleton_elim_name, 92);
library_constant_getter!(get_task_name, 93);
library_constant_getter!(get_thunk_name, 94);
library_constant_getter!(get_thunk_mk_name, 95);
library_constant_getter!(get_thunk_get_name, 96);
library_constant_getter!(get_true_name, 97);
library_constant_getter!(get_true_intro_name, 98);
library_constant_getter!(get_unit_name, 99);
library_constant_getter!(get_unit_unit_name, 100);
library_constant_getter!(get_uint8_name, 101);
library_constant_getter!(get_uint16_name, 102);
library_constant_getter!(get_uint32_name, 103);
library_constant_getter!(get_uint64_name, 104);
library_constant_getter!(get_usize_name, 105);
pub fn initialize_constants() {
    unsafe {
        for (index, path) in LIBRARY_CONSTANT_PATHS.iter().enumerate() {
            let value = mk_name_path(path);
            lean_mark_persistent(value.obj);
            LIBRARY_CONSTANTS[index] = value;
        }
    }
}
