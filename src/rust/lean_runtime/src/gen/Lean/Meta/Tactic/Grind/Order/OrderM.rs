// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.OrderM
// Imports: Lean.Meta.Tactic.Grind.Order.Types
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_getIntExpr___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::Types::{
    initialize_Lean_Meta_Tactic_Grind_Order_Types, l_Lean_Meta_Grind_Order_get_x27___redArg,
    l_Lean_Meta_Grind_Order_orderExt, runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_sub, lean_usize_to_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_12, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Meta_Grind_Order_getStruct___closed__0_value: LeanStringObject<51> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101,
            114, 114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 111, 114, 100, 101,
            114, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 105, 100, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Order_getStruct___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getStruct___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Order_getStruct___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_getStruct___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Grind_Order_getNodeId___closed__0_value: LeanStringObject<71> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 71,
        m_capacity: 71,
        m_length: 70,
        m_data: [
            105, 110, 116, 101, 114, 110, 97, 108, 32, 96, 103, 114, 105, 110, 100, 96, 32, 101,
            114, 114, 111, 114, 44, 32, 116, 101, 114, 109, 32, 104, 97, 115, 32, 110, 111, 116,
            32, 98, 101, 101, 110, 32, 105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 100,
            32, 98, 121, 32, 111, 114, 100, 101, 114, 32, 109, 111, 100, 117, 108, 101, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getNodeId___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_getProof___closed__0_value: LeanStringObject<54> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 54,
        m_capacity: 54,
        m_length: 53,
        m_data: [
            105, 110, 116, 101, 114, 110, 97, 108, 32, 96, 103, 114, 105, 110, 100, 96, 32, 101,
            114, 114, 111, 114, 44, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111,
            110, 115, 116, 114, 117, 99, 116, 32, 112, 114, 111, 111, 102, 32, 102, 111, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Order_getProof___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getProof___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Order_getProof___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_getProof___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_getProof___closed__2_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [10, 97, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Order_getProof___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getProof___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Order_getProof___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_getProof___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___redArg(
    mut v_structId_1002_: *mut LeanObject,
    mut v_x_1003_: *mut LeanObject,
    mut v_a_1004_: *mut LeanObject,
    mut v_a_1005_: *mut LeanObject,
    mut v_a_1006_: *mut LeanObject,
    mut v_a_1007_: *mut LeanObject,
    mut v_a_1008_: *mut LeanObject,
    mut v_a_1009_: *mut LeanObject,
    mut v_a_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
    mut v_a_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_1013_);
    lean_inc_ref(v_a_1012_);
    lean_inc(v_a_1011_);
    lean_inc_ref(v_a_1010_);
    lean_inc(v_a_1009_);
    lean_inc_ref(v_a_1008_);
    lean_inc(v_a_1007_);
    lean_inc_ref(v_a_1006_);
    lean_inc(v_a_1005_);
    lean_inc(v_a_1004_);
    v___x_1015_ = lean_apply_12(
        v_x_1003_,
        v_structId_1002_,
        v_a_1004_,
        v_a_1005_,
        v_a_1006_,
        v_a_1007_,
        v_a_1008_,
        v_a_1009_,
        v_a_1010_,
        v_a_1011_,
        v_a_1012_,
        v_a_1013_,
        lean_box(0),
    );
    return v___x_1015_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___redArg___boxed(
    mut v_structId_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
    mut v_a_1018_: *mut LeanObject,
    mut v_a_1019_: *mut LeanObject,
    mut v_a_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
    mut v_a_1023_: *mut LeanObject,
    mut v_a_1024_: *mut LeanObject,
    mut v_a_1025_: *mut LeanObject,
    mut v_a_1026_: *mut LeanObject,
    mut v_a_1027_: *mut LeanObject,
    mut v_a_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1029_: *mut LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Lean_Meta_Grind_Order_OrderM_run___redArg(
        v_structId_1016_,
        v_x_1017_,
        v_a_1018_,
        v_a_1019_,
        v_a_1020_,
        v_a_1021_,
        v_a_1022_,
        v_a_1023_,
        v_a_1024_,
        v_a_1025_,
        v_a_1026_,
        v_a_1027_,
    );
    lean_dec(v_a_1027_);
    lean_dec_ref(v_a_1026_);
    lean_dec(v_a_1025_);
    lean_dec_ref(v_a_1024_);
    lean_dec(v_a_1023_);
    lean_dec_ref(v_a_1022_);
    lean_dec(v_a_1021_);
    lean_dec_ref(v_a_1020_);
    lean_dec(v_a_1019_);
    lean_dec(v_a_1018_);
    return v_res_1029_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run(
    mut v_00_u03b1_1030_: *mut LeanObject,
    mut v_structId_1031_: *mut LeanObject,
    mut v_x_1032_: *mut LeanObject,
    mut v_a_1033_: *mut LeanObject,
    mut v_a_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
    mut v_a_1041_: *mut LeanObject,
    mut v_a_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_1042_);
    lean_inc_ref(v_a_1041_);
    lean_inc(v_a_1040_);
    lean_inc_ref(v_a_1039_);
    lean_inc(v_a_1038_);
    lean_inc_ref(v_a_1037_);
    lean_inc(v_a_1036_);
    lean_inc_ref(v_a_1035_);
    lean_inc(v_a_1034_);
    lean_inc(v_a_1033_);
    v___x_1044_ = lean_apply_12(
        v_x_1032_,
        v_structId_1031_,
        v_a_1033_,
        v_a_1034_,
        v_a_1035_,
        v_a_1036_,
        v_a_1037_,
        v_a_1038_,
        v_a_1039_,
        v_a_1040_,
        v_a_1041_,
        v_a_1042_,
        lean_box(0),
    );
    return v___x_1044_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___boxed(
    mut v_00_u03b1_1045_: *mut LeanObject,
    mut v_structId_1046_: *mut LeanObject,
    mut v_x_1047_: *mut LeanObject,
    mut v_a_1048_: *mut LeanObject,
    mut v_a_1049_: *mut LeanObject,
    mut v_a_1050_: *mut LeanObject,
    mut v_a_1051_: *mut LeanObject,
    mut v_a_1052_: *mut LeanObject,
    mut v_a_1053_: *mut LeanObject,
    mut v_a_1054_: *mut LeanObject,
    mut v_a_1055_: *mut LeanObject,
    mut v_a_1056_: *mut LeanObject,
    mut v_a_1057_: *mut LeanObject,
    mut v_a_1058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1059_: *mut LeanObject = core::ptr::null_mut();
    v_res_1059_ = l_Lean_Meta_Grind_Order_OrderM_run(
        v_00_u03b1_1045_,
        v_structId_1046_,
        v_x_1047_,
        v_a_1048_,
        v_a_1049_,
        v_a_1050_,
        v_a_1051_,
        v_a_1052_,
        v_a_1053_,
        v_a_1054_,
        v_a_1055_,
        v_a_1056_,
        v_a_1057_,
    );
    lean_dec(v_a_1057_);
    lean_dec_ref(v_a_1056_);
    lean_dec(v_a_1055_);
    lean_dec_ref(v_a_1054_);
    lean_dec(v_a_1053_);
    lean_dec_ref(v_a_1052_);
    lean_dec(v_a_1051_);
    lean_dec_ref(v_a_1050_);
    lean_dec(v_a_1049_);
    lean_dec(v_a_1048_);
    return v_res_1059_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___redArg(
    mut v_a_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_1060_);
    v___x_1062_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1062_, 0, v_a_1060_);
    return v___x_1062_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___redArg___boxed(
    mut v_a_1063_: *mut LeanObject,
    mut v_a_1064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1065_: *mut LeanObject = core::ptr::null_mut();
    v_res_1065_ = l_Lean_Meta_Grind_Order_getStructId___redArg(v_a_1063_);
    lean_dec(v_a_1063_);
    return v_res_1065_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId(
    mut v_a_1066_: *mut LeanObject,
    mut v_a_1067_: *mut LeanObject,
    mut v_a_1068_: *mut LeanObject,
    mut v_a_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
    mut v_a_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_1066_);
    v___x_1078_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1078_, 0, v_a_1066_);
    return v___x_1078_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___boxed(
    mut v_a_1079_: *mut LeanObject,
    mut v_a_1080_: *mut LeanObject,
    mut v_a_1081_: *mut LeanObject,
    mut v_a_1082_: *mut LeanObject,
    mut v_a_1083_: *mut LeanObject,
    mut v_a_1084_: *mut LeanObject,
    mut v_a_1085_: *mut LeanObject,
    mut v_a_1086_: *mut LeanObject,
    mut v_a_1087_: *mut LeanObject,
    mut v_a_1088_: *mut LeanObject,
    mut v_a_1089_: *mut LeanObject,
    mut v_a_1090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1091_: *mut LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_Lean_Meta_Grind_Order_getStructId(
        v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_,
        v_a_1087_, v_a_1088_, v_a_1089_,
    );
    lean_dec(v_a_1089_);
    lean_dec_ref(v_a_1088_);
    lean_dec(v_a_1087_);
    lean_dec_ref(v_a_1086_);
    lean_dec(v_a_1085_);
    lean_dec_ref(v_a_1084_);
    lean_dec(v_a_1083_);
    lean_dec_ref(v_a_1082_);
    lean_dec(v_a_1081_);
    lean_dec(v_a_1080_);
    lean_dec(v_a_1079_);
    return v_res_1091_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(
    mut v_msgData_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
    mut v___y_1094_: *mut LeanObject,
    mut v___y_1095_: *mut LeanObject,
    mut v___y_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    v___x_1098_ = lean_st_ref_get(v___y_1096_);
    v_env_1099_ = lean_ctor_get(v___x_1098_, 0);
    lean_inc_ref(v_env_1099_);
    lean_dec(v___x_1098_);
    v___x_1100_ = lean_st_ref_get(v___y_1094_);
    v_mctx_1101_ = lean_ctor_get(v___x_1100_, 0);
    lean_inc_ref(v_mctx_1101_);
    lean_dec(v___x_1100_);
    v_lctx_1102_ = lean_ctor_get(v___y_1093_, 2);
    v_options_1103_ = lean_ctor_get(v___y_1095_, 2);
    lean_inc_ref(v_options_1103_);
    lean_inc_ref(v_lctx_1102_);
    v___x_1104_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1104_, 0, v_env_1099_);
    lean_ctor_set(v___x_1104_, 1, v_mctx_1101_);
    lean_ctor_set(v___x_1104_, 2, v_lctx_1102_);
    lean_ctor_set(v___x_1104_, 3, v_options_1103_);
    v___x_1105_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    lean_ctor_set(v___x_1105_, 1, v_msgData_1092_);
    v___x_1106_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1106_, 0, v___x_1105_);
    return v___x_1106_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0___boxed(
    mut v_msgData_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
    mut v___y_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1113_: *mut LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(v_msgData_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
    lean_dec(v___y_1111_);
    lean_dec_ref(v___y_1110_);
    lean_dec(v___y_1109_);
    lean_dec_ref(v___y_1108_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
    mut v_msg_1114_: *mut LeanObject,
    mut v___y_1115_: *mut LeanObject,
    mut v___y_1116_: *mut LeanObject,
    mut v___y_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1125_: u8 = 0;
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1120_ = lean_ctor_get(v___y_1117_, 5);
                v___x_1121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(v_msg_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
                v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
                v_isSharedCheck_1130_ = (!lean_is_exclusive(v___x_1121_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v___x_1124_ = v___x_1121_;
                    v_isShared_1125_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1122_);
                    lean_dec(v___x_1121_);
                    v___x_1124_ = lean_box(0);
                    v_isShared_1125_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1120_);
                v___x_1126_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1126_, 0, v_ref_1120_);
                lean_ctor_set(v___x_1126_, 1, v_a_1122_);
                if v_isShared_1125_ == 0 {
                    lean_ctor_set_tag(v___x_1124_, 1);
                    lean_ctor_set(v___x_1124_, 0, v___x_1126_);
                    v___x_1128_ = v___x_1124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
                    v___x_1128_ = v_reuseFailAlloc_1129_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg___boxed(
    mut v_msg_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1137_: *mut LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
        v_msg_1131_,
        v___y_1132_,
        v___y_1133_,
        v___y_1134_,
        v___y_1135_,
    );
    lean_dec(v___y_1135_);
    lean_dec_ref(v___y_1134_);
    lean_dec(v___y_1133_);
    lean_dec_ref(v___y_1132_);
    return v_res_1137_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getStruct___closed__1() -> *mut LeanObject {
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    v___x_1139_ = l_Lean_Meta_Grind_Order_getStruct___closed__0;
    v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
    return v___x_1140_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStruct(
    mut v_a_1141_: *mut LeanObject,
    mut v_a_1142_: *mut LeanObject,
    mut v_a_1143_: *mut LeanObject,
    mut v_a_1144_: *mut LeanObject,
    mut v_a_1145_: *mut LeanObject,
    mut v_a_1146_: *mut LeanObject,
    mut v_a_1147_: *mut LeanObject,
    mut v_a_1148_: *mut LeanObject,
    mut v_a_1149_: *mut LeanObject,
    mut v_a_1150_: *mut LeanObject,
    mut v_a_1151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v_structs_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v_a_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1153_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1142_, v_a_1150_);
                if lean_obj_tag(v___x_1153_) == 0 {
                    v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
                    v_isSharedCheck_1167_ = (!lean_is_exclusive(v___x_1153_)) as u8;
                    if v_isSharedCheck_1167_ == 0 {
                        v___x_1156_ = v___x_1153_;
                        v_isShared_1157_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1154_);
                        lean_dec(v___x_1153_);
                        v___x_1156_ = lean_box(0);
                        v_isShared_1157_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1168_ = lean_ctor_get(v___x_1153_, 0);
                    v_isSharedCheck_1175_ = (!lean_is_exclusive(v___x_1153_)) as u8;
                    if v_isSharedCheck_1175_ == 0 {
                        v___x_1170_ = v___x_1153_;
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1168_);
                        lean_dec(v___x_1153_);
                        v___x_1170_ = lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_structs_1158_ = lean_ctor_get(v_a_1154_, 0);
                lean_inc_ref(v_structs_1158_);
                lean_dec(v_a_1154_);
                v___x_1159_ = lean_array_get_size(v_structs_1158_);
                v___x_1160_ = lean_nat_dec_lt(v_a_1141_, v___x_1159_);
                if v___x_1160_ == 0 {
                    lean_dec_ref(v_structs_1158_);
                    lean_del_object(v___x_1156_);
                    v___x_1161_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_getStruct___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_getStruct___closed__1_once),
                        _init_l_Lean_Meta_Grind_Order_getStruct___closed__1,
                    );
                    v___x_1162_ =
                        l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
                            v___x_1161_,
                            v_a_1148_,
                            v_a_1149_,
                            v_a_1150_,
                            v_a_1151_,
                        );
                    return v___x_1162_;
                } else {
                    v___x_1163_ = lean_array_fget(v_structs_1158_, v_a_1141_);
                    lean_dec_ref(v_structs_1158_);
                    if v_isShared_1157_ == 0 {
                        lean_ctor_set(v___x_1156_, 0, v___x_1163_);
                        v___x_1165_ = v___x_1156_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
                        v___x_1165_ = v_reuseFailAlloc_1166_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1165_;
            }
            3 => {
                if v_isShared_1171_ == 0 {
                    v___x_1173_ = v___x_1170_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
                    v___x_1173_ = v_reuseFailAlloc_1174_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStruct___boxed(
    mut v_a_1176_: *mut LeanObject,
    mut v_a_1177_: *mut LeanObject,
    mut v_a_1178_: *mut LeanObject,
    mut v_a_1179_: *mut LeanObject,
    mut v_a_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_a_1182_: *mut LeanObject,
    mut v_a_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1188_: *mut LeanObject = core::ptr::null_mut();
    v_res_1188_ = l_Lean_Meta_Grind_Order_getStruct(
        v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_,
        v_a_1184_, v_a_1185_, v_a_1186_,
    );
    lean_dec(v_a_1186_);
    lean_dec_ref(v_a_1185_);
    lean_dec(v_a_1184_);
    lean_dec_ref(v_a_1183_);
    lean_dec(v_a_1182_);
    lean_dec_ref(v_a_1181_);
    lean_dec(v_a_1180_);
    lean_dec_ref(v_a_1179_);
    lean_dec(v_a_1178_);
    lean_dec(v_a_1177_);
    lean_dec(v_a_1176_);
    return v_res_1188_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0(
    mut v_00_u03b1_1189_: *mut LeanObject,
    mut v_msg_1190_: *mut LeanObject,
    mut v___y_1191_: *mut LeanObject,
    mut v___y_1192_: *mut LeanObject,
    mut v___y_1193_: *mut LeanObject,
    mut v___y_1194_: *mut LeanObject,
    mut v___y_1195_: *mut LeanObject,
    mut v___y_1196_: *mut LeanObject,
    mut v___y_1197_: *mut LeanObject,
    mut v___y_1198_: *mut LeanObject,
    mut v___y_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
    mut v___y_1201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
        v_msg_1190_,
        v___y_1198_,
        v___y_1199_,
        v___y_1200_,
        v___y_1201_,
    );
    return v___x_1203_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___boxed(
    mut v_00_u03b1_1204_: *mut LeanObject,
    mut v_msg_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
    mut v___y_1207_: *mut LeanObject,
    mut v___y_1208_: *mut LeanObject,
    mut v___y_1209_: *mut LeanObject,
    mut v___y_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1218_: *mut LeanObject = core::ptr::null_mut();
    v_res_1218_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0(
        v_00_u03b1_1204_,
        v_msg_1205_,
        v___y_1206_,
        v___y_1207_,
        v___y_1208_,
        v___y_1209_,
        v___y_1210_,
        v___y_1211_,
        v___y_1212_,
        v___y_1213_,
        v___y_1214_,
        v___y_1215_,
        v___y_1216_,
    );
    lean_dec(v___y_1216_);
    lean_dec_ref(v___y_1215_);
    lean_dec(v___y_1214_);
    lean_dec_ref(v___y_1213_);
    lean_dec(v___y_1212_);
    lean_dec_ref(v___y_1211_);
    lean_dec(v___y_1210_);
    lean_dec_ref(v___y_1209_);
    lean_dec(v___y_1208_);
    lean_dec(v___y_1207_);
    lean_dec(v___y_1206_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(
    mut v_a_1219_: *mut LeanObject,
    mut v_f_1220_: *mut LeanObject,
    mut v_s_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termMap_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termMapInv_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v_v_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_1222_ = lean_ctor_get(v_s_1221_, 0);
                v_typeIdOf_1223_ = lean_ctor_get(v_s_1221_, 1);
                v_exprToStructId_1224_ = lean_ctor_get(v_s_1221_, 2);
                v_termMap_1225_ = lean_ctor_get(v_s_1221_, 3);
                v_termMapInv_1226_ = lean_ctor_get(v_s_1221_, 4);
                v___x_1227_ = lean_array_get_size(v_structs_1222_);
                v___x_1228_ = lean_nat_dec_lt(v_a_1219_, v___x_1227_);
                if v___x_1228_ == 0 {
                    lean_dec_ref(v_f_1220_);
                    return v_s_1221_;
                } else {
                    lean_inc_ref(v_termMapInv_1226_);
                    lean_inc_ref(v_termMap_1225_);
                    lean_inc_ref(v_exprToStructId_1224_);
                    lean_inc_ref(v_typeIdOf_1223_);
                    lean_inc_ref(v_structs_1222_);
                    v_isSharedCheck_1240_ = (!lean_is_exclusive(v_s_1221_)) as u8;
                    if v_isSharedCheck_1240_ == 0 {
                        v_unused_1241_ = lean_ctor_get(v_s_1221_, 4);
                        lean_dec(v_unused_1241_);
                        v_unused_1242_ = lean_ctor_get(v_s_1221_, 3);
                        lean_dec(v_unused_1242_);
                        v_unused_1243_ = lean_ctor_get(v_s_1221_, 2);
                        lean_dec(v_unused_1243_);
                        v_unused_1244_ = lean_ctor_get(v_s_1221_, 1);
                        lean_dec(v_unused_1244_);
                        v_unused_1245_ = lean_ctor_get(v_s_1221_, 0);
                        lean_dec(v_unused_1245_);
                        v___x_1230_ = v_s_1221_;
                        v_isShared_1231_ = v_isSharedCheck_1240_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_1221_);
                        v___x_1230_ = lean_box(0);
                        v_isShared_1231_ = v_isSharedCheck_1240_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1232_ = lean_array_fget(v_structs_1222_, v_a_1219_);
                v___x_1233_ = lean_box(0);
                v_xs_x27_1234_ = lean_array_fset(v_structs_1222_, v_a_1219_, v___x_1233_);
                v___x_1235_ = lean_apply_1(v_f_1220_, v_v_1232_);
                v___x_1236_ = lean_array_fset(v_xs_x27_1234_, v_a_1219_, v___x_1235_);
                if v_isShared_1231_ == 0 {
                    lean_ctor_set(v___x_1230_, 0, v___x_1236_);
                    v___x_1238_ = v___x_1230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_typeIdOf_1223_);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_exprToStructId_1224_);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_termMap_1225_);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_termMapInv_1226_);
                    v___x_1238_ = v_reuseFailAlloc_1239_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed(
    mut v_a_1246_: *mut LeanObject,
    mut v_f_1247_: *mut LeanObject,
    mut v_s_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1249_ =
        l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(v_a_1246_, v_f_1247_, v_s_1248_);
    lean_dec(v_a_1246_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg(
    mut v_f_1250_: *mut LeanObject,
    mut v_a_1251_: *mut LeanObject,
    mut v_a_1252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_1251_);
    v___f_1254_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1254_, 0, v_a_1251_);
    lean_closure_set(v___f_1254_, 1, v_f_1250_);
    v___x_1255_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_1256_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1255_, v___f_1254_, v_a_1252_);
    return v___x_1256_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg___boxed(
    mut v_f_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1261_: *mut LeanObject = core::ptr::null_mut();
    v_res_1261_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_1257_, v_a_1258_, v_a_1259_);
    lean_dec(v_a_1259_);
    lean_dec(v_a_1258_);
    return v_res_1261_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct(
    mut v_f_1262_: *mut LeanObject,
    mut v_a_1263_: *mut LeanObject,
    mut v_a_1264_: *mut LeanObject,
    mut v_a_1265_: *mut LeanObject,
    mut v_a_1266_: *mut LeanObject,
    mut v_a_1267_: *mut LeanObject,
    mut v_a_1268_: *mut LeanObject,
    mut v_a_1269_: *mut LeanObject,
    mut v_a_1270_: *mut LeanObject,
    mut v_a_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_1262_, v_a_1263_, v_a_1264_);
    return v___x_1275_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___boxed(
    mut v_f_1276_: *mut LeanObject,
    mut v_a_1277_: *mut LeanObject,
    mut v_a_1278_: *mut LeanObject,
    mut v_a_1279_: *mut LeanObject,
    mut v_a_1280_: *mut LeanObject,
    mut v_a_1281_: *mut LeanObject,
    mut v_a_1282_: *mut LeanObject,
    mut v_a_1283_: *mut LeanObject,
    mut v_a_1284_: *mut LeanObject,
    mut v_a_1285_: *mut LeanObject,
    mut v_a_1286_: *mut LeanObject,
    mut v_a_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1289_: *mut LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Lean_Meta_Grind_Order_modifyStruct(
        v_f_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_,
        v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_,
    );
    lean_dec(v_a_1287_);
    lean_dec_ref(v_a_1286_);
    lean_dec(v_a_1285_);
    lean_dec_ref(v_a_1284_);
    lean_dec(v_a_1283_);
    lean_dec_ref(v_a_1282_);
    lean_dec(v_a_1281_);
    lean_dec_ref(v_a_1280_);
    lean_dec(v_a_1279_);
    lean_dec(v_a_1278_);
    lean_dec(v_a_1277_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getExpr(
    mut v_u_1290_: *mut LeanObject,
    mut v_a_1291_: *mut LeanObject,
    mut v_a_1292_: *mut LeanObject,
    mut v_a_1293_: *mut LeanObject,
    mut v_a_1294_: *mut LeanObject,
    mut v_a_1295_: *mut LeanObject,
    mut v_a_1296_: *mut LeanObject,
    mut v_a_1297_: *mut LeanObject,
    mut v_a_1298_: *mut LeanObject,
    mut v_a_1299_: *mut LeanObject,
    mut v_a_1300_: *mut LeanObject,
    mut v_a_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v_nodes_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_a_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1303_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_,
                    v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_,
                );
                if lean_obj_tag(v___x_1303_) == 0 {
                    v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
                    v_isSharedCheck_1320_ = (!lean_is_exclusive(v___x_1303_)) as u8;
                    if v_isSharedCheck_1320_ == 0 {
                        v___x_1306_ = v___x_1303_;
                        v_isShared_1307_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1304_);
                        lean_dec(v___x_1303_);
                        v___x_1306_ = lean_box(0);
                        v_isShared_1307_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1321_ = lean_ctor_get(v___x_1303_, 0);
                    v_isSharedCheck_1328_ = (!lean_is_exclusive(v___x_1303_)) as u8;
                    if v_isSharedCheck_1328_ == 0 {
                        v___x_1323_ = v___x_1303_;
                        v_isShared_1324_ = v_isSharedCheck_1328_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1321_);
                        lean_dec(v___x_1303_);
                        v___x_1323_ = lean_box(0);
                        v_isShared_1324_ = v_isSharedCheck_1328_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_nodes_1308_ = lean_ctor_get(v_a_1304_, 14);
                lean_inc_ref(v_nodes_1308_);
                lean_dec(v_a_1304_);
                v_size_1309_ = lean_ctor_get(v_nodes_1308_, 2);
                v___x_1310_ = l_Lean_instInhabitedExpr;
                v___x_1311_ = lean_nat_dec_lt(v_u_1290_, v_size_1309_);
                if v___x_1311_ == 0 {
                    lean_dec_ref(v_nodes_1308_);
                    v___x_1312_ = l_outOfBounds___redArg(v___x_1310_);
                    if v_isShared_1307_ == 0 {
                        lean_ctor_set(v___x_1306_, 0, v___x_1312_);
                        v___x_1314_ = v___x_1306_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
                        v___x_1314_ = v_reuseFailAlloc_1315_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1316_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1310_,
                        v_nodes_1308_,
                        v_u_1290_,
                    );
                    lean_dec_ref(v_nodes_1308_);
                    if v_isShared_1307_ == 0 {
                        lean_ctor_set(v___x_1306_, 0, v___x_1316_);
                        v___x_1318_ = v___x_1306_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
                        v___x_1318_ = v_reuseFailAlloc_1319_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1314_;
            }
            3 => {
                return v___x_1318_;
            }
            4 => {
                if v_isShared_1324_ == 0 {
                    v___x_1326_ = v___x_1323_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
                    v___x_1326_ = v_reuseFailAlloc_1327_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_getExpr___boxed(
    mut v_u_1329_: *mut LeanObject,
    mut v_a_1330_: *mut LeanObject,
    mut v_a_1331_: *mut LeanObject,
    mut v_a_1332_: *mut LeanObject,
    mut v_a_1333_: *mut LeanObject,
    mut v_a_1334_: *mut LeanObject,
    mut v_a_1335_: *mut LeanObject,
    mut v_a_1336_: *mut LeanObject,
    mut v_a_1337_: *mut LeanObject,
    mut v_a_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
    mut v_a_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1342_: *mut LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_Lean_Meta_Grind_Order_getExpr(
        v_u_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_,
        v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_,
    );
    lean_dec(v_a_1340_);
    lean_dec_ref(v_a_1339_);
    lean_dec(v_a_1338_);
    lean_dec_ref(v_a_1337_);
    lean_dec(v_a_1336_);
    lean_dec_ref(v_a_1335_);
    lean_dec(v_a_1334_);
    lean_dec_ref(v_a_1333_);
    lean_dec(v_a_1332_);
    lean_dec(v_a_1331_);
    lean_dec(v_a_1330_);
    lean_dec(v_u_1329_);
    return v_res_1342_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
    mut v_a_1343_: *mut LeanObject,
    mut v_x_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1344_) == 0 {
                    v___x_1345_ = lean_box(0);
                    return v___x_1345_;
                } else {
                    v_key_1346_ = lean_ctor_get(v_x_1344_, 0);
                    v_value_1347_ = lean_ctor_get(v_x_1344_, 1);
                    v_tail_1348_ = lean_ctor_get(v_x_1344_, 2);
                    v___x_1349_ = lean_nat_dec_eq(v_key_1346_, v_a_1343_);
                    if v___x_1349_ == 0 {
                        v_x_1344_ = v_tail_1348_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1347_);
                        v___x_1351_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1351_, 0, v_value_1347_);
                        return v___x_1351_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg___boxed(
    mut v_a_1352_: *mut LeanObject,
    mut v_x_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1354_: *mut LeanObject = core::ptr::null_mut();
    v_res_1354_ =
        l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
            v_a_1352_, v_x_1353_,
        );
    lean_dec(v_x_1353_);
    lean_dec(v_a_1352_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getDist_x3f(
    mut v_u_1355_: *mut LeanObject,
    mut v_v_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
    mut v_a_1358_: *mut LeanObject,
    mut v_a_1359_: *mut LeanObject,
    mut v_a_1360_: *mut LeanObject,
    mut v_a_1361_: *mut LeanObject,
    mut v_a_1362_: *mut LeanObject,
    mut v_a_1363_: *mut LeanObject,
    mut v_a_1364_: *mut LeanObject,
    mut v_a_1365_: *mut LeanObject,
    mut v_a_1366_: *mut LeanObject,
    mut v_a_1367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v___y_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_targets_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1386_: u8 = 0;
    let mut v_a_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1369_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_,
                    v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_,
                );
                if lean_obj_tag(v___x_1369_) == 0 {
                    v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
                    v_isSharedCheck_1386_ = (!lean_is_exclusive(v___x_1369_)) as u8;
                    if v_isSharedCheck_1386_ == 0 {
                        v___x_1372_ = v___x_1369_;
                        v_isShared_1373_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1370_);
                        lean_dec(v___x_1369_);
                        v___x_1372_ = lean_box(0);
                        v_isShared_1373_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1387_ = lean_ctor_get(v___x_1369_, 0);
                    v_isSharedCheck_1394_ = (!lean_is_exclusive(v___x_1369_)) as u8;
                    if v_isSharedCheck_1394_ == 0 {
                        v___x_1389_ = v___x_1369_;
                        v_isShared_1390_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1387_);
                        lean_dec(v___x_1369_);
                        v___x_1389_ = lean_box(0);
                        v_isShared_1390_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_targets_1380_ = lean_ctor_get(v_a_1370_, 19);
                lean_inc_ref(v_targets_1380_);
                lean_dec(v_a_1370_);
                v_size_1381_ = lean_ctor_get(v_targets_1380_, 2);
                v___x_1382_ = lean_box(0);
                v___x_1383_ = lean_nat_dec_lt(v_u_1355_, v_size_1381_);
                if v___x_1383_ == 0 {
                    lean_dec_ref(v_targets_1380_);
                    v___x_1384_ = l_outOfBounds___redArg(v___x_1382_);
                    v___y_1375_ = v___x_1384_;
                    state = 2;
                    continue;
                } else {
                    v___x_1385_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1382_,
                        v_targets_1380_,
                        v_u_1355_,
                    );
                    lean_dec_ref(v_targets_1380_);
                    v___y_1375_ = v___x_1385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1376_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_1356_, v___y_1375_);
                lean_dec(v___y_1375_);
                if v_isShared_1373_ == 0 {
                    lean_ctor_set(v___x_1372_, 0, v___x_1376_);
                    v___x_1378_ = v___x_1372_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
                    v___x_1378_ = v_reuseFailAlloc_1379_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1378_;
            }
            4 => {
                if v_isShared_1390_ == 0 {
                    v___x_1392_ = v___x_1389_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
                    v___x_1392_ = v_reuseFailAlloc_1393_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1392_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_getDist_x3f___boxed(
    mut v_u_1395_: *mut LeanObject,
    mut v_v_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
    mut v_a_1402_: *mut LeanObject,
    mut v_a_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
    mut v_a_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_a_1407_: *mut LeanObject,
    mut v_a_1408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1409_: *mut LeanObject = core::ptr::null_mut();
    v_res_1409_ = l_Lean_Meta_Grind_Order_getDist_x3f(
        v_u_1395_, v_v_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_,
        v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_,
    );
    lean_dec(v_a_1407_);
    lean_dec_ref(v_a_1406_);
    lean_dec(v_a_1405_);
    lean_dec_ref(v_a_1404_);
    lean_dec(v_a_1403_);
    lean_dec_ref(v_a_1402_);
    lean_dec(v_a_1401_);
    lean_dec_ref(v_a_1400_);
    lean_dec(v_a_1399_);
    lean_dec(v_a_1398_);
    lean_dec(v_a_1397_);
    lean_dec(v_v_1396_);
    lean_dec(v_u_1395_);
    return v_res_1409_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(
    mut v_00_u03b2_1410_: *mut LeanObject,
    mut v_a_1411_: *mut LeanObject,
    mut v_x_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    v___x_1413_ =
        l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
            v_a_1411_, v_x_1412_,
        );
    return v___x_1413_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___boxed(
    mut v_00_u03b2_1414_: *mut LeanObject,
    mut v_a_1415_: *mut LeanObject,
    mut v_x_1416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1417_: *mut LeanObject = core::ptr::null_mut();
    v_res_1417_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(
        v_00_u03b2_1414_,
        v_a_1415_,
        v_x_1416_,
    );
    lean_dec(v_x_1416_);
    lean_dec(v_a_1415_);
    return v_res_1417_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getProof_x3f(
    mut v_u_1418_: *mut LeanObject,
    mut v_v_1419_: *mut LeanObject,
    mut v_a_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
    mut v_a_1422_: *mut LeanObject,
    mut v_a_1423_: *mut LeanObject,
    mut v_a_1424_: *mut LeanObject,
    mut v_a_1425_: *mut LeanObject,
    mut v_a_1426_: *mut LeanObject,
    mut v_a_1427_: *mut LeanObject,
    mut v_a_1428_: *mut LeanObject,
    mut v_a_1429_: *mut LeanObject,
    mut v_a_1430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1436_: u8 = 0;
    let mut v___y_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofs_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1449_: u8 = 0;
    let mut v_a_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1432_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_,
                    v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_,
                );
                if lean_obj_tag(v___x_1432_) == 0 {
                    v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
                    v_isSharedCheck_1449_ = (!lean_is_exclusive(v___x_1432_)) as u8;
                    if v_isSharedCheck_1449_ == 0 {
                        v___x_1435_ = v___x_1432_;
                        v_isShared_1436_ = v_isSharedCheck_1449_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1433_);
                        lean_dec(v___x_1432_);
                        v___x_1435_ = lean_box(0);
                        v_isShared_1436_ = v_isSharedCheck_1449_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1450_ = lean_ctor_get(v___x_1432_, 0);
                    v_isSharedCheck_1457_ = (!lean_is_exclusive(v___x_1432_)) as u8;
                    if v_isSharedCheck_1457_ == 0 {
                        v___x_1452_ = v___x_1432_;
                        v_isShared_1453_ = v_isSharedCheck_1457_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1450_);
                        lean_dec(v___x_1432_);
                        v___x_1452_ = lean_box(0);
                        v_isShared_1453_ = v_isSharedCheck_1457_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_proofs_1443_ = lean_ctor_get(v_a_1433_, 20);
                lean_inc_ref(v_proofs_1443_);
                lean_dec(v_a_1433_);
                v_size_1444_ = lean_ctor_get(v_proofs_1443_, 2);
                v___x_1445_ = lean_box(0);
                v___x_1446_ = lean_nat_dec_lt(v_u_1418_, v_size_1444_);
                if v___x_1446_ == 0 {
                    lean_dec_ref(v_proofs_1443_);
                    v___x_1447_ = l_outOfBounds___redArg(v___x_1445_);
                    v___y_1438_ = v___x_1447_;
                    state = 2;
                    continue;
                } else {
                    v___x_1448_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1445_,
                        v_proofs_1443_,
                        v_u_1418_,
                    );
                    lean_dec_ref(v_proofs_1443_);
                    v___y_1438_ = v___x_1448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1439_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_1419_, v___y_1438_);
                lean_dec(v___y_1438_);
                if v_isShared_1436_ == 0 {
                    lean_ctor_set(v___x_1435_, 0, v___x_1439_);
                    v___x_1441_ = v___x_1435_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
                    v___x_1441_ = v_reuseFailAlloc_1442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1441_;
            }
            4 => {
                if v_isShared_1453_ == 0 {
                    v___x_1455_ = v___x_1452_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
                    v___x_1455_ = v_reuseFailAlloc_1456_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_getProof_x3f___boxed(
    mut v_u_1458_: *mut LeanObject,
    mut v_v_1459_: *mut LeanObject,
    mut v_a_1460_: *mut LeanObject,
    mut v_a_1461_: *mut LeanObject,
    mut v_a_1462_: *mut LeanObject,
    mut v_a_1463_: *mut LeanObject,
    mut v_a_1464_: *mut LeanObject,
    mut v_a_1465_: *mut LeanObject,
    mut v_a_1466_: *mut LeanObject,
    mut v_a_1467_: *mut LeanObject,
    mut v_a_1468_: *mut LeanObject,
    mut v_a_1469_: *mut LeanObject,
    mut v_a_1470_: *mut LeanObject,
    mut v_a_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1472_: *mut LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Lean_Meta_Grind_Order_getProof_x3f(
        v_u_1458_, v_v_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_,
        v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_,
    );
    lean_dec(v_a_1470_);
    lean_dec_ref(v_a_1469_);
    lean_dec(v_a_1468_);
    lean_dec_ref(v_a_1467_);
    lean_dec(v_a_1466_);
    lean_dec_ref(v_a_1465_);
    lean_dec(v_a_1464_);
    lean_dec_ref(v_a_1463_);
    lean_dec(v_a_1462_);
    lean_dec(v_a_1461_);
    lean_dec(v_a_1460_);
    lean_dec(v_v_1459_);
    lean_dec(v_u_1458_);
    return v_res_1472_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1473_: *mut LeanObject,
    mut v_vals_1474_: *mut LeanObject,
    mut v_i_1475_: *mut LeanObject,
    mut v_k_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_array_get_size(v_keys_1473_);
                v___x_1478_ = lean_nat_dec_lt(v_i_1475_, v___x_1477_);
                if v___x_1478_ == 0 {
                    lean_dec(v_i_1475_);
                    v___x_1479_ = lean_box(0);
                    return v___x_1479_;
                } else {
                    v_k_x27_1480_ = lean_array_fget_borrowed(v_keys_1473_, v_i_1475_);
                    v___x_1481_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1476_,
                            v_k_x27_1480_,
                        );
                    if v___x_1481_ == 0 {
                        v___x_1482_ = lean_unsigned_to_nat(1);
                        v___x_1483_ = lean_nat_add(v_i_1475_, v___x_1482_);
                        lean_dec(v_i_1475_);
                        v_i_1475_ = v___x_1483_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1485_ = lean_array_fget_borrowed(v_vals_1474_, v_i_1475_);
                        lean_dec(v_i_1475_);
                        lean_inc(v___x_1485_);
                        v___x_1486_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1486_, 0, v___x_1485_);
                        return v___x_1486_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1487_: *mut LeanObject,
    mut v_vals_1488_: *mut LeanObject,
    mut v_i_1489_: *mut LeanObject,
    mut v_k_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1491_: *mut LeanObject = core::ptr::null_mut();
    v_res_1491_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_1487_, v_vals_1488_, v_i_1489_, v_k_1490_);
    lean_dec_ref(v_k_1490_);
    lean_dec_ref(v_vals_1488_);
    lean_dec_ref(v_keys_1487_);
    return v_res_1491_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1492_: usize = 0;
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    v___x_1492_ = 5usize;
    v___x_1493_ = 1usize;
    v___x_1494_ = lean_usize_shift_left(v___x_1493_, v___x_1492_);
    return v___x_1494_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1495_: usize = 0;
    let mut v___x_1496_: usize = 0;
    let mut v___x_1497_: usize = 0;
    v___x_1495_ = 1usize;
    v___x_1496_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0);
    v___x_1497_ = lean_usize_sub(v___x_1496_, v___x_1495_);
    return v___x_1497_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(
    mut v_x_1498_: *mut LeanObject,
    mut v_x_1499_: usize,
    mut v_x_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: usize = 0;
    let mut v___x_1505_: usize = 0;
    let mut v_j_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: usize = 0;
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1498_) == 0 {
                    v_es_1501_ = lean_ctor_get(v_x_1498_, 0);
                    v___x_1502_ = lean_box(2);
                    v___x_1503_ = 5usize;
                    v___x_1504_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1);
                    v___x_1505_ = lean_usize_land(v_x_1499_, v___x_1504_);
                    v_j_1506_ = lean_usize_to_nat(v___x_1505_);
                    v___x_1507_ = lean_array_get_borrowed(v___x_1502_, v_es_1501_, v_j_1506_);
                    lean_dec(v_j_1506_);
                    match lean_obj_tag(v___x_1507_) {
                        0 => {
                            v_key_1508_ = lean_ctor_get(v___x_1507_, 0);
                            v_val_1509_ = lean_ctor_get(v___x_1507_, 1);
                            v___x_1510_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1500_, v_key_1508_);
                            if v___x_1510_ == 0 {
                                v___x_1511_ = lean_box(0);
                                return v___x_1511_;
                            } else {
                                lean_inc(v_val_1509_);
                                v___x_1512_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1512_, 0, v_val_1509_);
                                return v___x_1512_;
                            }
                        }
                        1 => {
                            v_node_1513_ = lean_ctor_get(v___x_1507_, 0);
                            v___x_1514_ = lean_usize_shift_right(v_x_1499_, v___x_1503_);
                            v_x_1498_ = v_node_1513_;
                            v_x_1499_ = v___x_1514_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1516_ = lean_box(0);
                            return v___x_1516_;
                        }
                    }
                } else {
                    v_ks_1517_ = lean_ctor_get(v_x_1498_, 0);
                    v_vs_1518_ = lean_ctor_get(v_x_1498_, 1);
                    v___x_1519_ = lean_unsigned_to_nat(0);
                    v___x_1520_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_ks_1517_, v_vs_1518_, v___x_1519_, v_x_1500_);
                    return v___x_1520_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___boxed(
    mut v_x_1521_: *mut LeanObject,
    mut v_x_1522_: *mut LeanObject,
    mut v_x_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1311__boxed_1524_: usize = 0;
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_x_1311__boxed_1524_ = lean_unbox_usize(v_x_1522_);
    lean_dec(v_x_1522_);
    v_res_1525_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1521_, v_x_1311__boxed_1524_, v_x_1523_);
    lean_dec_ref(v_x_1523_);
    lean_dec_ref(v_x_1521_);
    return v_res_1525_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
    mut v_x_1526_: *mut LeanObject,
    mut v_x_1527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1528_: u64 = 0;
    let mut v___x_1529_: usize = 0;
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1527_);
    v___x_1529_ = lean_uint64_to_usize(v___x_1528_);
    v___x_1530_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1526_, v___x_1529_, v_x_1527_);
    return v___x_1530_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg___boxed(
    mut v_x_1531_: *mut LeanObject,
    mut v_x_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1533_: *mut LeanObject = core::ptr::null_mut();
    v_res_1533_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
            v_x_1531_, v_x_1532_,
        );
    lean_dec_ref(v_x_1532_);
    lean_dec_ref(v_x_1531_);
    return v_res_1533_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getNodeId___closed__1() -> *mut LeanObject {
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    v___x_1535_ = l_Lean_Meta_Grind_Order_getNodeId___closed__0;
    v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
    return v___x_1536_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getNodeId(
    mut v_e_1537_: *mut LeanObject,
    mut v_a_1538_: *mut LeanObject,
    mut v_a_1539_: *mut LeanObject,
    mut v_a_1540_: *mut LeanObject,
    mut v_a_1541_: *mut LeanObject,
    mut v_a_1542_: *mut LeanObject,
    mut v_a_1543_: *mut LeanObject,
    mut v_a_1544_: *mut LeanObject,
    mut v_a_1545_: *mut LeanObject,
    mut v_a_1546_: *mut LeanObject,
    mut v_a_1547_: *mut LeanObject,
    mut v_a_1548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v_nodeMap_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut v_a_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1550_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_,
                    v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_,
                );
                if lean_obj_tag(v___x_1550_) == 0 {
                    v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
                    v_isSharedCheck_1565_ = (!lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1565_ == 0 {
                        v___x_1553_ = v___x_1550_;
                        v_isShared_1554_ = v_isSharedCheck_1565_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1551_);
                        lean_dec(v___x_1550_);
                        v___x_1553_ = lean_box(0);
                        v_isShared_1554_ = v_isSharedCheck_1565_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1537_);
                    v_a_1566_ = lean_ctor_get(v___x_1550_, 0);
                    v_isSharedCheck_1573_ = (!lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v___x_1568_ = v___x_1550_;
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1566_);
                        lean_dec(v___x_1550_);
                        v___x_1568_ = lean_box(0);
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_nodeMap_1555_ = lean_ctor_get(v_a_1551_, 15);
                lean_inc_ref(v_nodeMap_1555_);
                lean_dec(v_a_1551_);
                v___x_1556_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_nodeMap_1555_, v_e_1537_);
                lean_dec_ref(v_nodeMap_1555_);
                if lean_obj_tag(v___x_1556_) == 1 {
                    lean_dec_ref(v_e_1537_);
                    v_val_1557_ = lean_ctor_get(v___x_1556_, 0);
                    lean_inc(v_val_1557_);
                    lean_dec_ref_known(v___x_1556_, 1);
                    if v_isShared_1554_ == 0 {
                        lean_ctor_set(v___x_1553_, 0, v_val_1557_);
                        v___x_1559_ = v___x_1553_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_val_1557_);
                        v___x_1559_ = v_reuseFailAlloc_1560_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1556_);
                    lean_del_object(v___x_1553_);
                    v___x_1561_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_getNodeId___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_getNodeId___closed__1_once),
                        _init_l_Lean_Meta_Grind_Order_getNodeId___closed__1,
                    );
                    v___x_1562_ = l_Lean_indentExpr(v_e_1537_);
                    v___x_1563_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1563_, 0, v___x_1561_);
                    lean_ctor_set(v___x_1563_, 1, v___x_1562_);
                    v___x_1564_ =
                        l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
                            v___x_1563_,
                            v_a_1545_,
                            v_a_1546_,
                            v_a_1547_,
                            v_a_1548_,
                        );
                    return v___x_1564_;
                }
            }
            2 => {
                return v___x_1559_;
            }
            3 => {
                if v_isShared_1569_ == 0 {
                    v___x_1571_ = v___x_1568_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
                    v___x_1571_ = v_reuseFailAlloc_1572_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_getNodeId___boxed(
    mut v_e_1574_: *mut LeanObject,
    mut v_a_1575_: *mut LeanObject,
    mut v_a_1576_: *mut LeanObject,
    mut v_a_1577_: *mut LeanObject,
    mut v_a_1578_: *mut LeanObject,
    mut v_a_1579_: *mut LeanObject,
    mut v_a_1580_: *mut LeanObject,
    mut v_a_1581_: *mut LeanObject,
    mut v_a_1582_: *mut LeanObject,
    mut v_a_1583_: *mut LeanObject,
    mut v_a_1584_: *mut LeanObject,
    mut v_a_1585_: *mut LeanObject,
    mut v_a_1586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1587_: *mut LeanObject = core::ptr::null_mut();
    v_res_1587_ = l_Lean_Meta_Grind_Order_getNodeId(
        v_e_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_,
        v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_,
    );
    lean_dec(v_a_1585_);
    lean_dec_ref(v_a_1584_);
    lean_dec(v_a_1583_);
    lean_dec_ref(v_a_1582_);
    lean_dec(v_a_1581_);
    lean_dec_ref(v_a_1580_);
    lean_dec(v_a_1579_);
    lean_dec_ref(v_a_1578_);
    lean_dec(v_a_1577_);
    lean_dec(v_a_1576_);
    lean_dec(v_a_1575_);
    return v_res_1587_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(
    mut v_00_u03b2_1588_: *mut LeanObject,
    mut v_x_1589_: *mut LeanObject,
    mut v_x_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    v___x_1591_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
            v_x_1589_, v_x_1590_,
        );
    return v___x_1591_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___boxed(
    mut v_00_u03b2_1592_: *mut LeanObject,
    mut v_x_1593_: *mut LeanObject,
    mut v_x_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1595_: *mut LeanObject = core::ptr::null_mut();
    v_res_1595_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(
            v_00_u03b2_1592_,
            v_x_1593_,
            v_x_1594_,
        );
    lean_dec_ref(v_x_1594_);
    lean_dec_ref(v_x_1593_);
    return v_res_1595_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(
    mut v_00_u03b2_1596_: *mut LeanObject,
    mut v_x_1597_: *mut LeanObject,
    mut v_x_1598_: usize,
    mut v_x_1599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1597_, v_x_1598_, v_x_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___boxed(
    mut v_00_u03b2_1601_: *mut LeanObject,
    mut v_x_1602_: *mut LeanObject,
    mut v_x_1603_: *mut LeanObject,
    mut v_x_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1442__boxed_1605_: usize = 0;
    let mut v_res_1606_: *mut LeanObject = core::ptr::null_mut();
    v_x_1442__boxed_1605_ = lean_unbox_usize(v_x_1603_);
    lean_dec(v_x_1603_);
    v_res_1606_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(v_00_u03b2_1601_, v_x_1602_, v_x_1442__boxed_1605_, v_x_1604_);
    lean_dec_ref(v_x_1604_);
    lean_dec_ref(v_x_1602_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1607_: *mut LeanObject,
    mut v_keys_1608_: *mut LeanObject,
    mut v_vals_1609_: *mut LeanObject,
    mut v_heq_1610_: *mut LeanObject,
    mut v_i_1611_: *mut LeanObject,
    mut v_k_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    v___x_1613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_1608_, v_vals_1609_, v_i_1611_, v_k_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1614_: *mut LeanObject,
    mut v_keys_1615_: *mut LeanObject,
    mut v_vals_1616_: *mut LeanObject,
    mut v_heq_1617_: *mut LeanObject,
    mut v_i_1618_: *mut LeanObject,
    mut v_k_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1620_: *mut LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(v_00_u03b2_1614_, v_keys_1615_, v_vals_1616_, v_heq_1617_, v_i_1618_, v_k_1619_);
    lean_dec_ref(v_k_1619_);
    lean_dec_ref(v_vals_1616_);
    lean_dec_ref(v_keys_1615_);
    return v_res_1620_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getProof___closed__1() -> *mut LeanObject {
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_Lean_Meta_Grind_Order_getProof___closed__0;
    v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getProof___closed__3() -> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_Meta_Grind_Order_getProof___closed__2;
    v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
    return v___x_1626_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getProof(
    mut v_u_1627_: *mut LeanObject,
    mut v_v_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
    mut v_a_1630_: *mut LeanObject,
    mut v_a_1631_: *mut LeanObject,
    mut v_a_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
    mut v_a_1634_: *mut LeanObject,
    mut v_a_1635_: *mut LeanObject,
    mut v_a_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
    mut v_a_1638_: *mut LeanObject,
    mut v_a_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v_val_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v_a_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1673_: u8 = 0;
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut v_isSharedCheck_1678_: u8 = 0;
    let mut v_a_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1641_ = l_Lean_Meta_Grind_Order_getProof_x3f(
                    v_u_1627_, v_v_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                    v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                );
                if lean_obj_tag(v___x_1641_) == 0 {
                    v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1678_ = (!lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1678_ == 0 {
                        v___x_1644_ = v___x_1641_;
                        v_isShared_1645_ = v_isSharedCheck_1678_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1642_);
                        lean_dec(v___x_1641_);
                        v___x_1644_ = lean_box(0);
                        v_isShared_1645_ = v_isSharedCheck_1678_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1679_ = lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1686_ = (!lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1686_ == 0 {
                        v___x_1681_ = v___x_1641_;
                        v_isShared_1682_ = v_isSharedCheck_1686_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1679_);
                        lean_dec(v___x_1641_);
                        v___x_1681_ = lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1686_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1642_) == 1 {
                    v_val_1646_ = lean_ctor_get(v_a_1642_, 0);
                    lean_inc(v_val_1646_);
                    lean_dec_ref_known(v_a_1642_, 1);
                    if v_isShared_1645_ == 0 {
                        lean_ctor_set(v___x_1644_, 0, v_val_1646_);
                        v___x_1648_ = v___x_1644_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1646_);
                        v___x_1648_ = v_reuseFailAlloc_1649_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1644_);
                    lean_dec(v_a_1642_);
                    v___x_1650_ = l_Lean_Meta_Grind_Order_getExpr(
                        v_u_1627_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                        v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                    );
                    if lean_obj_tag(v___x_1650_) == 0 {
                        v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
                        lean_inc(v_a_1651_);
                        lean_dec_ref_known(v___x_1650_, 1);
                        v___x_1652_ = l_Lean_Meta_Grind_Order_getExpr(
                            v_v_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                            v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                        );
                        if lean_obj_tag(v___x_1652_) == 0 {
                            v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
                            lean_inc(v_a_1653_);
                            lean_dec_ref_known(v___x_1652_, 1);
                            v___x_1654_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__1_once
                                ),
                                _init_l_Lean_Meta_Grind_Order_getProof___closed__1,
                            );
                            v___x_1655_ = l_Lean_indentExpr(v_a_1651_);
                            v___x_1656_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1656_, 0, v___x_1654_);
                            lean_ctor_set(v___x_1656_, 1, v___x_1655_);
                            v___x_1657_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__3_once
                                ),
                                _init_l_Lean_Meta_Grind_Order_getProof___closed__3,
                            );
                            v___x_1658_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1658_, 0, v___x_1656_);
                            lean_ctor_set(v___x_1658_, 1, v___x_1657_);
                            v___x_1659_ = l_Lean_indentExpr(v_a_1653_);
                            v___x_1660_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1660_, 0, v___x_1658_);
                            lean_ctor_set(v___x_1660_, 1, v___x_1659_);
                            v___x_1661_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(v___x_1660_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
                            return v___x_1661_;
                        } else {
                            lean_dec(v_a_1651_);
                            v_a_1662_ = lean_ctor_get(v___x_1652_, 0);
                            v_isSharedCheck_1669_ = (!lean_is_exclusive(v___x_1652_)) as u8;
                            if v_isSharedCheck_1669_ == 0 {
                                v___x_1664_ = v___x_1652_;
                                v_isShared_1665_ = v_isSharedCheck_1669_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1662_);
                                lean_dec(v___x_1652_);
                                v___x_1664_ = lean_box(0);
                                v_isShared_1665_ = v_isSharedCheck_1669_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_1670_ = lean_ctor_get(v___x_1650_, 0);
                        v_isSharedCheck_1677_ = (!lean_is_exclusive(v___x_1650_)) as u8;
                        if v_isSharedCheck_1677_ == 0 {
                            v___x_1672_ = v___x_1650_;
                            v_isShared_1673_ = v_isSharedCheck_1677_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1670_);
                            lean_dec(v___x_1650_);
                            v___x_1672_ = lean_box(0);
                            v_isShared_1673_ = v_isSharedCheck_1677_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1648_;
            }
            3 => {
                if v_isShared_1665_ == 0 {
                    v___x_1667_ = v___x_1664_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
                    v___x_1667_ = v_reuseFailAlloc_1668_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1667_;
            }
            5 => {
                if v_isShared_1673_ == 0 {
                    v___x_1675_ = v___x_1672_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
                    v___x_1675_ = v_reuseFailAlloc_1676_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1675_;
            }
            7 => {
                if v_isShared_1682_ == 0 {
                    v___x_1684_ = v___x_1681_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
                    v___x_1684_ = v_reuseFailAlloc_1685_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_getProof___boxed(
    mut v_u_1687_: *mut LeanObject,
    mut v_v_1688_: *mut LeanObject,
    mut v_a_1689_: *mut LeanObject,
    mut v_a_1690_: *mut LeanObject,
    mut v_a_1691_: *mut LeanObject,
    mut v_a_1692_: *mut LeanObject,
    mut v_a_1693_: *mut LeanObject,
    mut v_a_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
    mut v_a_1696_: *mut LeanObject,
    mut v_a_1697_: *mut LeanObject,
    mut v_a_1698_: *mut LeanObject,
    mut v_a_1699_: *mut LeanObject,
    mut v_a_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1701_: *mut LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lean_Meta_Grind_Order_getProof(
        v_u_1687_, v_v_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_,
        v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_,
    );
    lean_dec(v_a_1699_);
    lean_dec_ref(v_a_1698_);
    lean_dec(v_a_1697_);
    lean_dec_ref(v_a_1696_);
    lean_dec(v_a_1695_);
    lean_dec_ref(v_a_1694_);
    lean_dec(v_a_1693_);
    lean_dec_ref(v_a_1692_);
    lean_dec(v_a_1691_);
    lean_dec(v_a_1690_);
    lean_dec(v_a_1689_);
    lean_dec(v_v_1688_);
    lean_dec(v_u_1687_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getCnstr_x3f(
    mut v_e_1702_: *mut LeanObject,
    mut v_a_1703_: *mut LeanObject,
    mut v_a_1704_: *mut LeanObject,
    mut v_a_1705_: *mut LeanObject,
    mut v_a_1706_: *mut LeanObject,
    mut v_a_1707_: *mut LeanObject,
    mut v_a_1708_: *mut LeanObject,
    mut v_a_1709_: *mut LeanObject,
    mut v_a_1710_: *mut LeanObject,
    mut v_a_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
    mut v_a_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v_cnstrs_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1725_: u8 = 0;
    let mut v_a_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1715_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
                    v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_,
                );
                if lean_obj_tag(v___x_1715_) == 0 {
                    v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1725_ = (!lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1725_ == 0 {
                        v___x_1718_ = v___x_1715_;
                        v_isShared_1719_ = v_isSharedCheck_1725_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1716_);
                        lean_dec(v___x_1715_);
                        v___x_1718_ = lean_box(0);
                        v_isShared_1719_ = v_isSharedCheck_1725_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1726_ = lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1733_ = (!lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1733_ == 0 {
                        v___x_1728_ = v___x_1715_;
                        v_isShared_1729_ = v_isSharedCheck_1733_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1726_);
                        lean_dec(v___x_1715_);
                        v___x_1728_ = lean_box(0);
                        v_isShared_1729_ = v_isSharedCheck_1733_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_cnstrs_1720_ = lean_ctor_get(v_a_1716_, 16);
                lean_inc_ref(v_cnstrs_1720_);
                lean_dec(v_a_1716_);
                v___x_1721_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_cnstrs_1720_, v_e_1702_);
                lean_dec_ref(v_cnstrs_1720_);
                if v_isShared_1719_ == 0 {
                    lean_ctor_set(v___x_1718_, 0, v___x_1721_);
                    v___x_1723_ = v___x_1718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
                    v___x_1723_ = v_reuseFailAlloc_1724_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1723_;
            }
            3 => {
                if v_isShared_1729_ == 0 {
                    v___x_1731_ = v___x_1728_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
                    v___x_1731_ = v_reuseFailAlloc_1732_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_getCnstr_x3f___boxed(
    mut v_e_1734_: *mut LeanObject,
    mut v_a_1735_: *mut LeanObject,
    mut v_a_1736_: *mut LeanObject,
    mut v_a_1737_: *mut LeanObject,
    mut v_a_1738_: *mut LeanObject,
    mut v_a_1739_: *mut LeanObject,
    mut v_a_1740_: *mut LeanObject,
    mut v_a_1741_: *mut LeanObject,
    mut v_a_1742_: *mut LeanObject,
    mut v_a_1743_: *mut LeanObject,
    mut v_a_1744_: *mut LeanObject,
    mut v_a_1745_: *mut LeanObject,
    mut v_a_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1747_: *mut LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(
        v_e_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_,
        v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_,
    );
    lean_dec(v_a_1745_);
    lean_dec_ref(v_a_1744_);
    lean_dec(v_a_1743_);
    lean_dec_ref(v_a_1742_);
    lean_dec(v_a_1741_);
    lean_dec_ref(v_a_1740_);
    lean_dec(v_a_1739_);
    lean_dec_ref(v_a_1738_);
    lean_dec(v_a_1737_);
    lean_dec(v_a_1736_);
    lean_dec(v_a_1735_);
    lean_dec_ref(v_e_1734_);
    return v_res_1747_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isRing(
    mut v_a_1748_: *mut LeanObject,
    mut v_a_1749_: *mut LeanObject,
    mut v_a_1750_: *mut LeanObject,
    mut v_a_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
    mut v_a_1753_: *mut LeanObject,
    mut v_a_1754_: *mut LeanObject,
    mut v_a_1755_: *mut LeanObject,
    mut v_a_1756_: *mut LeanObject,
    mut v_a_1757_: *mut LeanObject,
    mut v_a_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v_ringId_x3f_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_a_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1760_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_,
                    v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_,
                );
                if lean_obj_tag(v___x_1760_) == 0 {
                    v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
                    v_isSharedCheck_1776_ = (!lean_is_exclusive(v___x_1760_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v___x_1763_ = v___x_1760_;
                        v_isShared_1764_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1761_);
                        lean_dec(v___x_1760_);
                        v___x_1763_ = lean_box(0);
                        v_isShared_1764_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1777_ = lean_ctor_get(v___x_1760_, 0);
                    v_isSharedCheck_1784_ = (!lean_is_exclusive(v___x_1760_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1779_ = v___x_1760_;
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1777_);
                        lean_dec(v___x_1760_);
                        v___x_1779_ = lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_ringId_x3f_1765_ = lean_ctor_get(v_a_1761_, 9);
                lean_inc(v_ringId_x3f_1765_);
                lean_dec(v_a_1761_);
                if lean_obj_tag(v_ringId_x3f_1765_) == 0 {
                    v___x_1766_ = 0;
                    v___x_1767_ = lean_box((v___x_1766_) as usize);
                    if v_isShared_1764_ == 0 {
                        lean_ctor_set(v___x_1763_, 0, v___x_1767_);
                        v___x_1769_ = v___x_1763_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
                        v___x_1769_ = v_reuseFailAlloc_1770_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_ringId_x3f_1765_, 1);
                    v___x_1771_ = 1;
                    v___x_1772_ = lean_box((v___x_1771_) as usize);
                    if v_isShared_1764_ == 0 {
                        lean_ctor_set(v___x_1763_, 0, v___x_1772_);
                        v___x_1774_ = v___x_1763_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
                        v___x_1774_ = v_reuseFailAlloc_1775_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1769_;
            }
            3 => {
                return v___x_1774_;
            }
            4 => {
                if v_isShared_1780_ == 0 {
                    v___x_1782_ = v___x_1779_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
                    v___x_1782_ = v_reuseFailAlloc_1783_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_isRing___boxed(
    mut v_a_1785_: *mut LeanObject,
    mut v_a_1786_: *mut LeanObject,
    mut v_a_1787_: *mut LeanObject,
    mut v_a_1788_: *mut LeanObject,
    mut v_a_1789_: *mut LeanObject,
    mut v_a_1790_: *mut LeanObject,
    mut v_a_1791_: *mut LeanObject,
    mut v_a_1792_: *mut LeanObject,
    mut v_a_1793_: *mut LeanObject,
    mut v_a_1794_: *mut LeanObject,
    mut v_a_1795_: *mut LeanObject,
    mut v_a_1796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1797_: *mut LeanObject = core::ptr::null_mut();
    v_res_1797_ = l_Lean_Meta_Grind_Order_isRing(
        v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_,
        v_a_1793_, v_a_1794_, v_a_1795_,
    );
    lean_dec(v_a_1795_);
    lean_dec_ref(v_a_1794_);
    lean_dec(v_a_1793_);
    lean_dec_ref(v_a_1792_);
    lean_dec(v_a_1791_);
    lean_dec_ref(v_a_1790_);
    lean_dec(v_a_1789_);
    lean_dec_ref(v_a_1788_);
    lean_dec(v_a_1787_);
    lean_dec(v_a_1786_);
    lean_dec(v_a_1785_);
    return v_res_1797_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isPartialOrder(
    mut v_a_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
    mut v_a_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
    mut v_a_1802_: *mut LeanObject,
    mut v_a_1803_: *mut LeanObject,
    mut v_a_1804_: *mut LeanObject,
    mut v_a_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v_isPartialInst_x3f_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v_a_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1810_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_,
                    v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_,
                );
                if lean_obj_tag(v___x_1810_) == 0 {
                    v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
                    v_isSharedCheck_1826_ = (!lean_is_exclusive(v___x_1810_)) as u8;
                    if v_isSharedCheck_1826_ == 0 {
                        v___x_1813_ = v___x_1810_;
                        v_isShared_1814_ = v_isSharedCheck_1826_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1811_);
                        lean_dec(v___x_1810_);
                        v___x_1813_ = lean_box(0);
                        v_isShared_1814_ = v_isSharedCheck_1826_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1827_ = lean_ctor_get(v___x_1810_, 0);
                    v_isSharedCheck_1834_ = (!lean_is_exclusive(v___x_1810_)) as u8;
                    if v_isSharedCheck_1834_ == 0 {
                        v___x_1829_ = v___x_1810_;
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1827_);
                        lean_dec(v___x_1810_);
                        v___x_1829_ = lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isPartialInst_x3f_1815_ = lean_ctor_get(v_a_1811_, 6);
                lean_inc(v_isPartialInst_x3f_1815_);
                lean_dec(v_a_1811_);
                if lean_obj_tag(v_isPartialInst_x3f_1815_) == 0 {
                    v___x_1816_ = 0;
                    v___x_1817_ = lean_box((v___x_1816_) as usize);
                    if v_isShared_1814_ == 0 {
                        lean_ctor_set(v___x_1813_, 0, v___x_1817_);
                        v___x_1819_ = v___x_1813_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                        v___x_1819_ = v_reuseFailAlloc_1820_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_isPartialInst_x3f_1815_, 1);
                    v___x_1821_ = 1;
                    v___x_1822_ = lean_box((v___x_1821_) as usize);
                    if v_isShared_1814_ == 0 {
                        lean_ctor_set(v___x_1813_, 0, v___x_1822_);
                        v___x_1824_ = v___x_1813_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
                        v___x_1824_ = v_reuseFailAlloc_1825_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1819_;
            }
            3 => {
                return v___x_1824_;
            }
            4 => {
                if v_isShared_1830_ == 0 {
                    v___x_1832_ = v___x_1829_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
                    v___x_1832_ = v_reuseFailAlloc_1833_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_isPartialOrder___boxed(
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
    mut v_a_1842_: *mut LeanObject,
    mut v_a_1843_: *mut LeanObject,
    mut v_a_1844_: *mut LeanObject,
    mut v_a_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1847_: *mut LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Lean_Meta_Grind_Order_isPartialOrder(
        v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_,
        v_a_1843_, v_a_1844_, v_a_1845_,
    );
    lean_dec(v_a_1845_);
    lean_dec_ref(v_a_1844_);
    lean_dec(v_a_1843_);
    lean_dec_ref(v_a_1842_);
    lean_dec(v_a_1841_);
    lean_dec_ref(v_a_1840_);
    lean_dec(v_a_1839_);
    lean_dec_ref(v_a_1838_);
    lean_dec(v_a_1837_);
    lean_dec(v_a_1836_);
    lean_dec(v_a_1835_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isLinearPreorder(
    mut v_a_1848_: *mut LeanObject,
    mut v_a_1849_: *mut LeanObject,
    mut v_a_1850_: *mut LeanObject,
    mut v_a_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_a_1857_: *mut LeanObject,
    mut v_a_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v_isLinearPreInst_x3f_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u8 = 0;
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u8 = 0;
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_a_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1860_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_,
                    v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_,
                );
                if lean_obj_tag(v___x_1860_) == 0 {
                    v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1876_ = (!lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1876_ == 0 {
                        v___x_1863_ = v___x_1860_;
                        v_isShared_1864_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1861_);
                        lean_dec(v___x_1860_);
                        v___x_1863_ = lean_box(0);
                        v_isShared_1864_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1877_ = lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1884_ = (!lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1884_ == 0 {
                        v___x_1879_ = v___x_1860_;
                        v_isShared_1880_ = v_isSharedCheck_1884_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1877_);
                        lean_dec(v___x_1860_);
                        v___x_1879_ = lean_box(0);
                        v_isShared_1880_ = v_isSharedCheck_1884_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isLinearPreInst_x3f_1865_ = lean_ctor_get(v_a_1861_, 7);
                lean_inc(v_isLinearPreInst_x3f_1865_);
                lean_dec(v_a_1861_);
                if lean_obj_tag(v_isLinearPreInst_x3f_1865_) == 0 {
                    v___x_1866_ = 0;
                    v___x_1867_ = lean_box((v___x_1866_) as usize);
                    if v_isShared_1864_ == 0 {
                        lean_ctor_set(v___x_1863_, 0, v___x_1867_);
                        v___x_1869_ = v___x_1863_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
                        v___x_1869_ = v_reuseFailAlloc_1870_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_isLinearPreInst_x3f_1865_, 1);
                    v___x_1871_ = 1;
                    v___x_1872_ = lean_box((v___x_1871_) as usize);
                    if v_isShared_1864_ == 0 {
                        lean_ctor_set(v___x_1863_, 0, v___x_1872_);
                        v___x_1874_ = v___x_1863_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
                        v___x_1874_ = v_reuseFailAlloc_1875_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1869_;
            }
            3 => {
                return v___x_1874_;
            }
            4 => {
                if v_isShared_1880_ == 0 {
                    v___x_1882_ = v___x_1879_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
                    v___x_1882_ = v_reuseFailAlloc_1883_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_isLinearPreorder___boxed(
    mut v_a_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
    mut v_a_1889_: *mut LeanObject,
    mut v_a_1890_: *mut LeanObject,
    mut v_a_1891_: *mut LeanObject,
    mut v_a_1892_: *mut LeanObject,
    mut v_a_1893_: *mut LeanObject,
    mut v_a_1894_: *mut LeanObject,
    mut v_a_1895_: *mut LeanObject,
    mut v_a_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lean_Meta_Grind_Order_isLinearPreorder(
        v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_,
        v_a_1893_, v_a_1894_, v_a_1895_,
    );
    lean_dec(v_a_1895_);
    lean_dec_ref(v_a_1894_);
    lean_dec(v_a_1893_);
    lean_dec_ref(v_a_1892_);
    lean_dec(v_a_1891_);
    lean_dec_ref(v_a_1890_);
    lean_dec(v_a_1889_);
    lean_dec_ref(v_a_1888_);
    lean_dec(v_a_1887_);
    lean_dec(v_a_1886_);
    lean_dec(v_a_1885_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_hasLt(
    mut v_a_1898_: *mut LeanObject,
    mut v_a_1899_: *mut LeanObject,
    mut v_a_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
    mut v_a_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
    mut v_a_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
    mut v_a_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v_lawfulOrderLTInst_x3f_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut v_a_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1910_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_,
                    v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_,
                );
                if lean_obj_tag(v___x_1910_) == 0 {
                    v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
                    v_isSharedCheck_1926_ = (!lean_is_exclusive(v___x_1910_)) as u8;
                    if v_isSharedCheck_1926_ == 0 {
                        v___x_1913_ = v___x_1910_;
                        v_isShared_1914_ = v_isSharedCheck_1926_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1911_);
                        lean_dec(v___x_1910_);
                        v___x_1913_ = lean_box(0);
                        v_isShared_1914_ = v_isSharedCheck_1926_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1927_ = lean_ctor_get(v___x_1910_, 0);
                    v_isSharedCheck_1934_ = (!lean_is_exclusive(v___x_1910_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1929_ = v___x_1910_;
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1927_);
                        lean_dec(v___x_1910_);
                        v___x_1929_ = lean_box(0);
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_lawfulOrderLTInst_x3f_1915_ = lean_ctor_get(v_a_1911_, 8);
                lean_inc(v_lawfulOrderLTInst_x3f_1915_);
                lean_dec(v_a_1911_);
                if lean_obj_tag(v_lawfulOrderLTInst_x3f_1915_) == 0 {
                    v___x_1916_ = 0;
                    v___x_1917_ = lean_box((v___x_1916_) as usize);
                    if v_isShared_1914_ == 0 {
                        lean_ctor_set(v___x_1913_, 0, v___x_1917_);
                        v___x_1919_ = v___x_1913_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
                        v___x_1919_ = v_reuseFailAlloc_1920_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1915_, 1);
                    v___x_1921_ = 1;
                    v___x_1922_ = lean_box((v___x_1921_) as usize);
                    if v_isShared_1914_ == 0 {
                        lean_ctor_set(v___x_1913_, 0, v___x_1922_);
                        v___x_1924_ = v___x_1913_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
                        v___x_1924_ = v_reuseFailAlloc_1925_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1919_;
            }
            3 => {
                return v___x_1924_;
            }
            4 => {
                if v_isShared_1930_ == 0 {
                    v___x_1932_ = v___x_1929_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
                    v___x_1932_ = v_reuseFailAlloc_1933_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_hasLt___boxed(
    mut v_a_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
    mut v_a_1938_: *mut LeanObject,
    mut v_a_1939_: *mut LeanObject,
    mut v_a_1940_: *mut LeanObject,
    mut v_a_1941_: *mut LeanObject,
    mut v_a_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
    mut v_a_1944_: *mut LeanObject,
    mut v_a_1945_: *mut LeanObject,
    mut v_a_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1947_: *mut LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_Lean_Meta_Grind_Order_hasLt(
        v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_,
        v_a_1943_, v_a_1944_, v_a_1945_,
    );
    lean_dec(v_a_1945_);
    lean_dec_ref(v_a_1944_);
    lean_dec(v_a_1943_);
    lean_dec_ref(v_a_1942_);
    lean_dec(v_a_1941_);
    lean_dec_ref(v_a_1940_);
    lean_dec(v_a_1939_);
    lean_dec_ref(v_a_1938_);
    lean_dec(v_a_1937_);
    lean_dec(v_a_1936_);
    lean_dec(v_a_1935_);
    return v_res_1947_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isInt(
    mut v_a_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
    mut v_a_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
    mut v_a_1953_: *mut LeanObject,
    mut v_a_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
    mut v_a_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v_type_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v_a_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1981_: u8 = 0;
    let mut v_a_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1960_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_,
                    v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_,
                );
                if lean_obj_tag(v___x_1960_) == 0 {
                    v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
                    lean_inc(v_a_1961_);
                    lean_dec_ref_known(v___x_1960_, 1);
                    v___x_1962_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_1953_);
                    if lean_obj_tag(v___x_1962_) == 0 {
                        v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_1973_ = (!lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_1973_ == 0 {
                            v___x_1965_ = v___x_1962_;
                            v_isShared_1966_ = v_isSharedCheck_1973_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1963_);
                            lean_dec(v___x_1962_);
                            v___x_1965_ = lean_box(0);
                            v_isShared_1966_ = v_isSharedCheck_1973_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1961_);
                        v_a_1974_ = lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_1981_ = (!lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_1981_ == 0 {
                            v___x_1976_ = v___x_1962_;
                            v_isShared_1977_ = v_isSharedCheck_1981_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1974_);
                            lean_dec(v___x_1962_);
                            v___x_1976_ = lean_box(0);
                            v_isShared_1977_ = v_isSharedCheck_1981_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1982_ = lean_ctor_get(v___x_1960_, 0);
                    v_isSharedCheck_1989_ = (!lean_is_exclusive(v___x_1960_)) as u8;
                    if v_isSharedCheck_1989_ == 0 {
                        v___x_1984_ = v___x_1960_;
                        v_isShared_1985_ = v_isSharedCheck_1989_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1982_);
                        lean_dec(v___x_1960_);
                        v___x_1984_ = lean_box(0);
                        v_isShared_1985_ = v_isSharedCheck_1989_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_type_1967_ = lean_ctor_get(v_a_1961_, 1);
                lean_inc_ref(v_type_1967_);
                lean_dec(v_a_1961_);
                v___x_1968_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_1967_,
                        v_a_1963_,
                    );
                lean_dec(v_a_1963_);
                lean_dec_ref(v_type_1967_);
                v___x_1969_ = lean_box((v___x_1968_) as usize);
                if v_isShared_1966_ == 0 {
                    lean_ctor_set(v___x_1965_, 0, v___x_1969_);
                    v___x_1971_ = v___x_1965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1971_;
            }
            3 => {
                if v_isShared_1977_ == 0 {
                    v___x_1979_ = v___x_1976_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
                    v___x_1979_ = v_reuseFailAlloc_1980_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1979_;
            }
            5 => {
                if v_isShared_1985_ == 0 {
                    v___x_1987_ = v___x_1984_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
                    v___x_1987_ = v_reuseFailAlloc_1988_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_isInt___boxed(
    mut v_a_1990_: *mut LeanObject,
    mut v_a_1991_: *mut LeanObject,
    mut v_a_1992_: *mut LeanObject,
    mut v_a_1993_: *mut LeanObject,
    mut v_a_1994_: *mut LeanObject,
    mut v_a_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
    mut v_a_1997_: *mut LeanObject,
    mut v_a_1998_: *mut LeanObject,
    mut v_a_1999_: *mut LeanObject,
    mut v_a_2000_: *mut LeanObject,
    mut v_a_2001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2002_: *mut LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_Meta_Grind_Order_isInt(
        v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_,
        v_a_1998_, v_a_1999_, v_a_2000_,
    );
    lean_dec(v_a_2000_);
    lean_dec_ref(v_a_1999_);
    lean_dec(v_a_1998_);
    lean_dec_ref(v_a_1997_);
    lean_dec(v_a_1996_);
    lean_dec_ref(v_a_1995_);
    lean_dec(v_a_1994_);
    lean_dec_ref(v_a_1993_);
    lean_dec(v_a_1992_);
    lean_dec(v_a_1991_);
    lean_dec(v_a_1990_);
    return v_res_2002_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
}
