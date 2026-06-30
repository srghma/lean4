// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.OrderM
// Imports: Lean.Meta.Tactic.Grind.Order.Types
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_st_ref_get,
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
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
pub static l_Lean_Meta_Grind_Order_getStruct___closed__0_value: leanh::LeanStringObject<51> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_getStruct___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getStruct___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_getStruct___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_getStruct___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Grind_Order_getNodeId___closed__0_value: leanh::LeanStringObject<71> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getNodeId___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_getProof___closed__0_value: leanh::LeanStringObject<54> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_getProof___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getProof___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_getProof___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_getProof___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_getProof___closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_getProof___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getProof___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_getProof___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_getProof___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___redArg(
    mut v_structId_1002_: *mut leanh::LeanObject,
    mut v_x_1003_: *mut leanh::LeanObject,
    mut v_a_1004_: *mut leanh::LeanObject,
    mut v_a_1005_: *mut leanh::LeanObject,
    mut v_a_1006_: *mut leanh::LeanObject,
    mut v_a_1007_: *mut leanh::LeanObject,
    mut v_a_1008_: *mut leanh::LeanObject,
    mut v_a_1009_: *mut leanh::LeanObject,
    mut v_a_1010_: *mut leanh::LeanObject,
    mut v_a_1011_: *mut leanh::LeanObject,
    mut v_a_1012_: *mut leanh::LeanObject,
    mut v_a_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1013_);
    leanh::lean_inc_ref(v_a_1012_);
    leanh::lean_inc(v_a_1011_);
    leanh::lean_inc_ref(v_a_1010_);
    leanh::lean_inc(v_a_1009_);
    leanh::lean_inc_ref(v_a_1008_);
    leanh::lean_inc(v_a_1007_);
    leanh::lean_inc_ref(v_a_1006_);
    leanh::lean_inc(v_a_1005_);
    leanh::lean_inc(v_a_1004_);
    v___x_1015_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_1015_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___redArg___boxed(
    mut v_structId_1016_: *mut leanh::LeanObject,
    mut v_x_1017_: *mut leanh::LeanObject,
    mut v_a_1018_: *mut leanh::LeanObject,
    mut v_a_1019_: *mut leanh::LeanObject,
    mut v_a_1020_: *mut leanh::LeanObject,
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_a_1022_: *mut leanh::LeanObject,
    mut v_a_1023_: *mut leanh::LeanObject,
    mut v_a_1024_: *mut leanh::LeanObject,
    mut v_a_1025_: *mut leanh::LeanObject,
    mut v_a_1026_: *mut leanh::LeanObject,
    mut v_a_1027_: *mut leanh::LeanObject,
    mut v_a_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1027_);
    leanh::lean_dec_ref(v_a_1026_);
    leanh::lean_dec(v_a_1025_);
    leanh::lean_dec_ref(v_a_1024_);
    leanh::lean_dec(v_a_1023_);
    leanh::lean_dec_ref(v_a_1022_);
    leanh::lean_dec(v_a_1021_);
    leanh::lean_dec_ref(v_a_1020_);
    leanh::lean_dec(v_a_1019_);
    leanh::lean_dec(v_a_1018_);
    return v_res_1029_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run(
    mut v_00_u03b1_1030_: *mut leanh::LeanObject,
    mut v_structId_1031_: *mut leanh::LeanObject,
    mut v_x_1032_: *mut leanh::LeanObject,
    mut v_a_1033_: *mut leanh::LeanObject,
    mut v_a_1034_: *mut leanh::LeanObject,
    mut v_a_1035_: *mut leanh::LeanObject,
    mut v_a_1036_: *mut leanh::LeanObject,
    mut v_a_1037_: *mut leanh::LeanObject,
    mut v_a_1038_: *mut leanh::LeanObject,
    mut v_a_1039_: *mut leanh::LeanObject,
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
    mut v_a_1042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1042_);
    leanh::lean_inc_ref(v_a_1041_);
    leanh::lean_inc(v_a_1040_);
    leanh::lean_inc_ref(v_a_1039_);
    leanh::lean_inc(v_a_1038_);
    leanh::lean_inc_ref(v_a_1037_);
    leanh::lean_inc(v_a_1036_);
    leanh::lean_inc_ref(v_a_1035_);
    leanh::lean_inc(v_a_1034_);
    leanh::lean_inc(v_a_1033_);
    v___x_1044_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_1044_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___boxed(
    mut v_00_u03b1_1045_: *mut leanh::LeanObject,
    mut v_structId_1046_: *mut leanh::LeanObject,
    mut v_x_1047_: *mut leanh::LeanObject,
    mut v_a_1048_: *mut leanh::LeanObject,
    mut v_a_1049_: *mut leanh::LeanObject,
    mut v_a_1050_: *mut leanh::LeanObject,
    mut v_a_1051_: *mut leanh::LeanObject,
    mut v_a_1052_: *mut leanh::LeanObject,
    mut v_a_1053_: *mut leanh::LeanObject,
    mut v_a_1054_: *mut leanh::LeanObject,
    mut v_a_1055_: *mut leanh::LeanObject,
    mut v_a_1056_: *mut leanh::LeanObject,
    mut v_a_1057_: *mut leanh::LeanObject,
    mut v_a_1058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1057_);
    leanh::lean_dec_ref(v_a_1056_);
    leanh::lean_dec(v_a_1055_);
    leanh::lean_dec_ref(v_a_1054_);
    leanh::lean_dec(v_a_1053_);
    leanh::lean_dec_ref(v_a_1052_);
    leanh::lean_dec(v_a_1051_);
    leanh::lean_dec_ref(v_a_1050_);
    leanh::lean_dec(v_a_1049_);
    leanh::lean_dec(v_a_1048_);
    return v_res_1059_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___redArg(
    mut v_a_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1060_);
    v___x_1062_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1062_, 0, v_a_1060_);
    return v___x_1062_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___redArg___boxed(
    mut v_a_1063_: *mut leanh::LeanObject,
    mut v_a_1064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1065_ = l_Lean_Meta_Grind_Order_getStructId___redArg(v_a_1063_);
    leanh::lean_dec(v_a_1063_);
    return v_res_1065_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId(
    mut v_a_1066_: *mut leanh::LeanObject,
    mut v_a_1067_: *mut leanh::LeanObject,
    mut v_a_1068_: *mut leanh::LeanObject,
    mut v_a_1069_: *mut leanh::LeanObject,
    mut v_a_1070_: *mut leanh::LeanObject,
    mut v_a_1071_: *mut leanh::LeanObject,
    mut v_a_1072_: *mut leanh::LeanObject,
    mut v_a_1073_: *mut leanh::LeanObject,
    mut v_a_1074_: *mut leanh::LeanObject,
    mut v_a_1075_: *mut leanh::LeanObject,
    mut v_a_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1066_);
    v___x_1078_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1078_, 0, v_a_1066_);
    return v___x_1078_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___boxed(
    mut v_a_1079_: *mut leanh::LeanObject,
    mut v_a_1080_: *mut leanh::LeanObject,
    mut v_a_1081_: *mut leanh::LeanObject,
    mut v_a_1082_: *mut leanh::LeanObject,
    mut v_a_1083_: *mut leanh::LeanObject,
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
    mut v_a_1086_: *mut leanh::LeanObject,
    mut v_a_1087_: *mut leanh::LeanObject,
    mut v_a_1088_: *mut leanh::LeanObject,
    mut v_a_1089_: *mut leanh::LeanObject,
    mut v_a_1090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_Lean_Meta_Grind_Order_getStructId(
        v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_,
        v_a_1087_, v_a_1088_, v_a_1089_,
    );
    leanh::lean_dec(v_a_1089_);
    leanh::lean_dec_ref(v_a_1088_);
    leanh::lean_dec(v_a_1087_);
    leanh::lean_dec_ref(v_a_1086_);
    leanh::lean_dec(v_a_1085_);
    leanh::lean_dec_ref(v_a_1084_);
    leanh::lean_dec(v_a_1083_);
    leanh::lean_dec_ref(v_a_1082_);
    leanh::lean_dec(v_a_1081_);
    leanh::lean_dec(v_a_1080_);
    leanh::lean_dec(v_a_1079_);
    return v_res_1091_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(
    mut v_msgData_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
    mut v___y_1094_: *mut leanh::LeanObject,
    mut v___y_1095_: *mut leanh::LeanObject,
    mut v___y_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = lean_st_ref_get(v___y_1096_);
    v_env_1099_ = leanh::lean_ctor_get(v___x_1098_, 0);
    leanh::lean_inc_ref(v_env_1099_);
    leanh::lean_dec(v___x_1098_);
    v___x_1100_ = lean_st_ref_get(v___y_1094_);
    v_mctx_1101_ = leanh::lean_ctor_get(v___x_1100_, 0);
    leanh::lean_inc_ref(v_mctx_1101_);
    leanh::lean_dec(v___x_1100_);
    v_lctx_1102_ = leanh::lean_ctor_get(v___y_1093_, 2);
    v_options_1103_ = leanh::lean_ctor_get(v___y_1095_, 2);
    leanh::lean_inc_ref(v_options_1103_);
    leanh::lean_inc_ref(v_lctx_1102_);
    v___x_1104_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1104_, 0, v_env_1099_);
    leanh::lean_ctor_set(v___x_1104_, 1, v_mctx_1101_);
    leanh::lean_ctor_set(v___x_1104_, 2, v_lctx_1102_);
    leanh::lean_ctor_set(v___x_1104_, 3, v_options_1103_);
    v___x_1105_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    leanh::lean_ctor_set(v___x_1105_, 1, v_msgData_1092_);
    v___x_1106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1106_, 0, v___x_1105_);
    return v___x_1106_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0___boxed(
    mut v_msgData_1107_: *mut leanh::LeanObject,
    mut v___y_1108_: *mut leanh::LeanObject,
    mut v___y_1109_: *mut leanh::LeanObject,
    mut v___y_1110_: *mut leanh::LeanObject,
    mut v___y_1111_: *mut leanh::LeanObject,
    mut v___y_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(v_msgData_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
    leanh::lean_dec(v___y_1111_);
    leanh::lean_dec_ref(v___y_1110_);
    leanh::lean_dec(v___y_1109_);
    leanh::lean_dec_ref(v___y_1108_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
    mut v_msg_1114_: *mut leanh::LeanObject,
    mut v___y_1115_: *mut leanh::LeanObject,
    mut v___y_1116_: *mut leanh::LeanObject,
    mut v___y_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1125_: u8 = 0;
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1120_ = leanh::lean_ctor_get(v___y_1117_, 5);
                v___x_1121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(v_msg_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
                v_a_1122_ = leanh::lean_ctor_get(v___x_1121_, 0);
                v_isSharedCheck_1130_ = (!leanh::lean_is_exclusive(v___x_1121_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v___x_1124_ = v___x_1121_;
                    v_isShared_1125_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1122_);
                    leanh::lean_dec(v___x_1121_);
                    v___x_1124_ = leanh::lean_box(0);
                    v_isShared_1125_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1120_);
                v___x_1126_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1126_, 0, v_ref_1120_);
                leanh::lean_ctor_set(v___x_1126_, 1, v_a_1122_);
                if v_isShared_1125_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1124_, 1);
                    leanh::lean_ctor_set(v___x_1124_, 0, v___x_1126_);
                    v___x_1128_ = v___x_1124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
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
    mut v_msg_1131_: *mut leanh::LeanObject,
    mut v___y_1132_: *mut leanh::LeanObject,
    mut v___y_1133_: *mut leanh::LeanObject,
    mut v___y_1134_: *mut leanh::LeanObject,
    mut v___y_1135_: *mut leanh::LeanObject,
    mut v___y_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
        v_msg_1131_,
        v___y_1132_,
        v___y_1133_,
        v___y_1134_,
        v___y_1135_,
    );
    leanh::lean_dec(v___y_1135_);
    leanh::lean_dec_ref(v___y_1134_);
    leanh::lean_dec(v___y_1133_);
    leanh::lean_dec_ref(v___y_1132_);
    return v_res_1137_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getStruct___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1139_ = l_Lean_Meta_Grind_Order_getStruct___closed__0;
    v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
    return v___x_1140_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStruct(
    mut v_a_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
    mut v_a_1143_: *mut leanh::LeanObject,
    mut v_a_1144_: *mut leanh::LeanObject,
    mut v_a_1145_: *mut leanh::LeanObject,
    mut v_a_1146_: *mut leanh::LeanObject,
    mut v_a_1147_: *mut leanh::LeanObject,
    mut v_a_1148_: *mut leanh::LeanObject,
    mut v_a_1149_: *mut leanh::LeanObject,
    mut v_a_1150_: *mut leanh::LeanObject,
    mut v_a_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v_structs_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v_a_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1153_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1142_, v_a_1150_);
                if leanh::lean_obj_tag(v___x_1153_) == 0 {
                    v_a_1154_ = leanh::lean_ctor_get(v___x_1153_, 0);
                    v_isSharedCheck_1167_ = (!leanh::lean_is_exclusive(v___x_1153_)) as u8;
                    if v_isSharedCheck_1167_ == 0 {
                        v___x_1156_ = v___x_1153_;
                        v_isShared_1157_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1154_);
                        leanh::lean_dec(v___x_1153_);
                        v___x_1156_ = leanh::lean_box(0);
                        v_isShared_1157_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1168_ = leanh::lean_ctor_get(v___x_1153_, 0);
                    v_isSharedCheck_1175_ = (!leanh::lean_is_exclusive(v___x_1153_)) as u8;
                    if v_isSharedCheck_1175_ == 0 {
                        v___x_1170_ = v___x_1153_;
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1168_);
                        leanh::lean_dec(v___x_1153_);
                        v___x_1170_ = leanh::lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_structs_1158_ = leanh::lean_ctor_get(v_a_1154_, 0);
                leanh::lean_inc_ref(v_structs_1158_);
                leanh::lean_dec(v_a_1154_);
                v___x_1159_ = lean_array_get_size(v_structs_1158_);
                v___x_1160_ = lean_nat_dec_lt(v_a_1141_, v___x_1159_);
                if v___x_1160_ == 0 {
                    leanh::lean_dec_ref(v_structs_1158_);
                    leanh::lean_del_object(v___x_1156_);
                    v___x_1161_ = leanh::lean_obj_once(
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
                    leanh::lean_dec_ref(v_structs_1158_);
                    if v_isShared_1157_ == 0 {
                        leanh::lean_ctor_set(v___x_1156_, 0, v___x_1163_);
                        v___x_1165_ = v___x_1156_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1166_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
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
                    v_reuseFailAlloc_1174_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
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
    mut v_a_1176_: *mut leanh::LeanObject,
    mut v_a_1177_: *mut leanh::LeanObject,
    mut v_a_1178_: *mut leanh::LeanObject,
    mut v_a_1179_: *mut leanh::LeanObject,
    mut v_a_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
    mut v_a_1182_: *mut leanh::LeanObject,
    mut v_a_1183_: *mut leanh::LeanObject,
    mut v_a_1184_: *mut leanh::LeanObject,
    mut v_a_1185_: *mut leanh::LeanObject,
    mut v_a_1186_: *mut leanh::LeanObject,
    mut v_a_1187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1188_ = l_Lean_Meta_Grind_Order_getStruct(
        v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_,
        v_a_1184_, v_a_1185_, v_a_1186_,
    );
    leanh::lean_dec(v_a_1186_);
    leanh::lean_dec_ref(v_a_1185_);
    leanh::lean_dec(v_a_1184_);
    leanh::lean_dec_ref(v_a_1183_);
    leanh::lean_dec(v_a_1182_);
    leanh::lean_dec_ref(v_a_1181_);
    leanh::lean_dec(v_a_1180_);
    leanh::lean_dec_ref(v_a_1179_);
    leanh::lean_dec(v_a_1178_);
    leanh::lean_dec(v_a_1177_);
    leanh::lean_dec(v_a_1176_);
    return v_res_1188_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0(
    mut v_00_u03b1_1189_: *mut leanh::LeanObject,
    mut v_msg_1190_: *mut leanh::LeanObject,
    mut v___y_1191_: *mut leanh::LeanObject,
    mut v___y_1192_: *mut leanh::LeanObject,
    mut v___y_1193_: *mut leanh::LeanObject,
    mut v___y_1194_: *mut leanh::LeanObject,
    mut v___y_1195_: *mut leanh::LeanObject,
    mut v___y_1196_: *mut leanh::LeanObject,
    mut v___y_1197_: *mut leanh::LeanObject,
    mut v___y_1198_: *mut leanh::LeanObject,
    mut v___y_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
    mut v___y_1201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1204_: *mut leanh::LeanObject,
    mut v_msg_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
    mut v___y_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
    mut v___y_1211_: *mut leanh::LeanObject,
    mut v___y_1212_: *mut leanh::LeanObject,
    mut v___y_1213_: *mut leanh::LeanObject,
    mut v___y_1214_: *mut leanh::LeanObject,
    mut v___y_1215_: *mut leanh::LeanObject,
    mut v___y_1216_: *mut leanh::LeanObject,
    mut v___y_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1216_);
    leanh::lean_dec_ref(v___y_1215_);
    leanh::lean_dec(v___y_1214_);
    leanh::lean_dec_ref(v___y_1213_);
    leanh::lean_dec(v___y_1212_);
    leanh::lean_dec_ref(v___y_1211_);
    leanh::lean_dec(v___y_1210_);
    leanh::lean_dec_ref(v___y_1209_);
    leanh::lean_dec(v___y_1208_);
    leanh::lean_dec(v___y_1207_);
    leanh::lean_dec(v___y_1206_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(
    mut v_a_1219_: *mut leanh::LeanObject,
    mut v_f_1220_: *mut leanh::LeanObject,
    mut v_s_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMap_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMapInv_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v_v_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_1222_ = leanh::lean_ctor_get(v_s_1221_, 0);
                v_typeIdOf_1223_ = leanh::lean_ctor_get(v_s_1221_, 1);
                v_exprToStructId_1224_ = leanh::lean_ctor_get(v_s_1221_, 2);
                v_termMap_1225_ = leanh::lean_ctor_get(v_s_1221_, 3);
                v_termMapInv_1226_ = leanh::lean_ctor_get(v_s_1221_, 4);
                v___x_1227_ = lean_array_get_size(v_structs_1222_);
                v___x_1228_ = lean_nat_dec_lt(v_a_1219_, v___x_1227_);
                if v___x_1228_ == 0 {
                    leanh::lean_dec_ref(v_f_1220_);
                    return v_s_1221_;
                } else {
                    leanh::lean_inc_ref(v_termMapInv_1226_);
                    leanh::lean_inc_ref(v_termMap_1225_);
                    leanh::lean_inc_ref(v_exprToStructId_1224_);
                    leanh::lean_inc_ref(v_typeIdOf_1223_);
                    leanh::lean_inc_ref(v_structs_1222_);
                    v_isSharedCheck_1240_ = (!leanh::lean_is_exclusive(v_s_1221_)) as u8;
                    if v_isSharedCheck_1240_ == 0 {
                        v_unused_1241_ = leanh::lean_ctor_get(v_s_1221_, 4);
                        leanh::lean_dec(v_unused_1241_);
                        v_unused_1242_ = leanh::lean_ctor_get(v_s_1221_, 3);
                        leanh::lean_dec(v_unused_1242_);
                        v_unused_1243_ = leanh::lean_ctor_get(v_s_1221_, 2);
                        leanh::lean_dec(v_unused_1243_);
                        v_unused_1244_ = leanh::lean_ctor_get(v_s_1221_, 1);
                        leanh::lean_dec(v_unused_1244_);
                        v_unused_1245_ = leanh::lean_ctor_get(v_s_1221_, 0);
                        leanh::lean_dec(v_unused_1245_);
                        v___x_1230_ = v_s_1221_;
                        v_isShared_1231_ = v_isSharedCheck_1240_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_1221_);
                        v___x_1230_ = leanh::lean_box(0);
                        v_isShared_1231_ = v_isSharedCheck_1240_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1232_ = lean_array_fget(v_structs_1222_, v_a_1219_);
                v___x_1233_ = leanh::lean_box(0);
                v_xs_x27_1234_ = lean_array_fset(v_structs_1222_, v_a_1219_, v___x_1233_);
                v___x_1235_ = leanh::lean_apply_1(v_f_1220_, v_v_1232_);
                v___x_1236_ = lean_array_fset(v_xs_x27_1234_, v_a_1219_, v___x_1235_);
                if v_isShared_1231_ == 0 {
                    leanh::lean_ctor_set(v___x_1230_, 0, v___x_1236_);
                    v___x_1238_ = v___x_1230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_typeIdOf_1223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_exprToStructId_1224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_termMap_1225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_termMapInv_1226_);
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
    mut v_a_1246_: *mut leanh::LeanObject,
    mut v_f_1247_: *mut leanh::LeanObject,
    mut v_s_1248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ =
        l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(v_a_1246_, v_f_1247_, v_s_1248_);
    leanh::lean_dec(v_a_1246_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg(
    mut v_f_1250_: *mut leanh::LeanObject,
    mut v_a_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1251_);
    v___f_1254_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1254_, 0, v_a_1251_);
    leanh::lean_closure_set(v___f_1254_, 1, v_f_1250_);
    v___x_1255_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_1256_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1255_, v___f_1254_, v_a_1252_);
    return v___x_1256_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg___boxed(
    mut v_f_1257_: *mut leanh::LeanObject,
    mut v_a_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v_a_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_1257_, v_a_1258_, v_a_1259_);
    leanh::lean_dec(v_a_1259_);
    leanh::lean_dec(v_a_1258_);
    return v_res_1261_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct(
    mut v_f_1262_: *mut leanh::LeanObject,
    mut v_a_1263_: *mut leanh::LeanObject,
    mut v_a_1264_: *mut leanh::LeanObject,
    mut v_a_1265_: *mut leanh::LeanObject,
    mut v_a_1266_: *mut leanh::LeanObject,
    mut v_a_1267_: *mut leanh::LeanObject,
    mut v_a_1268_: *mut leanh::LeanObject,
    mut v_a_1269_: *mut leanh::LeanObject,
    mut v_a_1270_: *mut leanh::LeanObject,
    mut v_a_1271_: *mut leanh::LeanObject,
    mut v_a_1272_: *mut leanh::LeanObject,
    mut v_a_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_1262_, v_a_1263_, v_a_1264_);
    return v___x_1275_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___boxed(
    mut v_f_1276_: *mut leanh::LeanObject,
    mut v_a_1277_: *mut leanh::LeanObject,
    mut v_a_1278_: *mut leanh::LeanObject,
    mut v_a_1279_: *mut leanh::LeanObject,
    mut v_a_1280_: *mut leanh::LeanObject,
    mut v_a_1281_: *mut leanh::LeanObject,
    mut v_a_1282_: *mut leanh::LeanObject,
    mut v_a_1283_: *mut leanh::LeanObject,
    mut v_a_1284_: *mut leanh::LeanObject,
    mut v_a_1285_: *mut leanh::LeanObject,
    mut v_a_1286_: *mut leanh::LeanObject,
    mut v_a_1287_: *mut leanh::LeanObject,
    mut v_a_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Lean_Meta_Grind_Order_modifyStruct(
        v_f_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_,
        v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_,
    );
    leanh::lean_dec(v_a_1287_);
    leanh::lean_dec_ref(v_a_1286_);
    leanh::lean_dec(v_a_1285_);
    leanh::lean_dec_ref(v_a_1284_);
    leanh::lean_dec(v_a_1283_);
    leanh::lean_dec_ref(v_a_1282_);
    leanh::lean_dec(v_a_1281_);
    leanh::lean_dec_ref(v_a_1280_);
    leanh::lean_dec(v_a_1279_);
    leanh::lean_dec(v_a_1278_);
    leanh::lean_dec(v_a_1277_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getExpr(
    mut v_u_1290_: *mut leanh::LeanObject,
    mut v_a_1291_: *mut leanh::LeanObject,
    mut v_a_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
    mut v_a_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: *mut leanh::LeanObject,
    mut v_a_1296_: *mut leanh::LeanObject,
    mut v_a_1297_: *mut leanh::LeanObject,
    mut v_a_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
    mut v_a_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v_nodes_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_a_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1303_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_,
                    v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_,
                );
                if leanh::lean_obj_tag(v___x_1303_) == 0 {
                    v_a_1304_ = leanh::lean_ctor_get(v___x_1303_, 0);
                    v_isSharedCheck_1320_ = (!leanh::lean_is_exclusive(v___x_1303_)) as u8;
                    if v_isSharedCheck_1320_ == 0 {
                        v___x_1306_ = v___x_1303_;
                        v_isShared_1307_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1304_);
                        leanh::lean_dec(v___x_1303_);
                        v___x_1306_ = leanh::lean_box(0);
                        v_isShared_1307_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1321_ = leanh::lean_ctor_get(v___x_1303_, 0);
                    v_isSharedCheck_1328_ = (!leanh::lean_is_exclusive(v___x_1303_)) as u8;
                    if v_isSharedCheck_1328_ == 0 {
                        v___x_1323_ = v___x_1303_;
                        v_isShared_1324_ = v_isSharedCheck_1328_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1321_);
                        leanh::lean_dec(v___x_1303_);
                        v___x_1323_ = leanh::lean_box(0);
                        v_isShared_1324_ = v_isSharedCheck_1328_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_nodes_1308_ = leanh::lean_ctor_get(v_a_1304_, 14);
                leanh::lean_inc_ref(v_nodes_1308_);
                leanh::lean_dec(v_a_1304_);
                v_size_1309_ = leanh::lean_ctor_get(v_nodes_1308_, 2);
                v___x_1310_ = l_Lean_instInhabitedExpr;
                v___x_1311_ = lean_nat_dec_lt(v_u_1290_, v_size_1309_);
                if v___x_1311_ == 0 {
                    leanh::lean_dec_ref(v_nodes_1308_);
                    v___x_1312_ = l_outOfBounds___redArg(v___x_1310_);
                    if v_isShared_1307_ == 0 {
                        leanh::lean_ctor_set(v___x_1306_, 0, v___x_1312_);
                        v___x_1314_ = v___x_1306_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
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
                    leanh::lean_dec_ref(v_nodes_1308_);
                    if v_isShared_1307_ == 0 {
                        leanh::lean_ctor_set(v___x_1306_, 0, v___x_1316_);
                        v___x_1318_ = v___x_1306_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
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
                    v_reuseFailAlloc_1327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
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
    mut v_u_1329_: *mut leanh::LeanObject,
    mut v_a_1330_: *mut leanh::LeanObject,
    mut v_a_1331_: *mut leanh::LeanObject,
    mut v_a_1332_: *mut leanh::LeanObject,
    mut v_a_1333_: *mut leanh::LeanObject,
    mut v_a_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
    mut v_a_1337_: *mut leanh::LeanObject,
    mut v_a_1338_: *mut leanh::LeanObject,
    mut v_a_1339_: *mut leanh::LeanObject,
    mut v_a_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_Lean_Meta_Grind_Order_getExpr(
        v_u_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_,
        v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_,
    );
    leanh::lean_dec(v_a_1340_);
    leanh::lean_dec_ref(v_a_1339_);
    leanh::lean_dec(v_a_1338_);
    leanh::lean_dec_ref(v_a_1337_);
    leanh::lean_dec(v_a_1336_);
    leanh::lean_dec_ref(v_a_1335_);
    leanh::lean_dec(v_a_1334_);
    leanh::lean_dec_ref(v_a_1333_);
    leanh::lean_dec(v_a_1332_);
    leanh::lean_dec(v_a_1331_);
    leanh::lean_dec(v_a_1330_);
    leanh::lean_dec(v_u_1329_);
    return v_res_1342_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
    mut v_a_1343_: *mut leanh::LeanObject,
    mut v_x_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1344_) == 0 {
                    v___x_1345_ = leanh::lean_box(0);
                    return v___x_1345_;
                } else {
                    v_key_1346_ = leanh::lean_ctor_get(v_x_1344_, 0);
                    v_value_1347_ = leanh::lean_ctor_get(v_x_1344_, 1);
                    v_tail_1348_ = leanh::lean_ctor_get(v_x_1344_, 2);
                    v___x_1349_ = lean_nat_dec_eq(v_key_1346_, v_a_1343_);
                    if v___x_1349_ == 0 {
                        v_x_1344_ = v_tail_1348_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1347_);
                        v___x_1351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1351_, 0, v_value_1347_);
                        return v___x_1351_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg___boxed(
    mut v_a_1352_: *mut leanh::LeanObject,
    mut v_x_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ =
        l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
            v_a_1352_, v_x_1353_,
        );
    leanh::lean_dec(v_x_1353_);
    leanh::lean_dec(v_a_1352_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getDist_x3f(
    mut v_u_1355_: *mut leanh::LeanObject,
    mut v_v_1356_: *mut leanh::LeanObject,
    mut v_a_1357_: *mut leanh::LeanObject,
    mut v_a_1358_: *mut leanh::LeanObject,
    mut v_a_1359_: *mut leanh::LeanObject,
    mut v_a_1360_: *mut leanh::LeanObject,
    mut v_a_1361_: *mut leanh::LeanObject,
    mut v_a_1362_: *mut leanh::LeanObject,
    mut v_a_1363_: *mut leanh::LeanObject,
    mut v_a_1364_: *mut leanh::LeanObject,
    mut v_a_1365_: *mut leanh::LeanObject,
    mut v_a_1366_: *mut leanh::LeanObject,
    mut v_a_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v___y_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_targets_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1386_: u8 = 0;
    let mut v_a_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1369_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_,
                    v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_,
                );
                if leanh::lean_obj_tag(v___x_1369_) == 0 {
                    v_a_1370_ = leanh::lean_ctor_get(v___x_1369_, 0);
                    v_isSharedCheck_1386_ = (!leanh::lean_is_exclusive(v___x_1369_)) as u8;
                    if v_isSharedCheck_1386_ == 0 {
                        v___x_1372_ = v___x_1369_;
                        v_isShared_1373_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1370_);
                        leanh::lean_dec(v___x_1369_);
                        v___x_1372_ = leanh::lean_box(0);
                        v_isShared_1373_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1387_ = leanh::lean_ctor_get(v___x_1369_, 0);
                    v_isSharedCheck_1394_ = (!leanh::lean_is_exclusive(v___x_1369_)) as u8;
                    if v_isSharedCheck_1394_ == 0 {
                        v___x_1389_ = v___x_1369_;
                        v_isShared_1390_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1387_);
                        leanh::lean_dec(v___x_1369_);
                        v___x_1389_ = leanh::lean_box(0);
                        v_isShared_1390_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_targets_1380_ = leanh::lean_ctor_get(v_a_1370_, 19);
                leanh::lean_inc_ref(v_targets_1380_);
                leanh::lean_dec(v_a_1370_);
                v_size_1381_ = leanh::lean_ctor_get(v_targets_1380_, 2);
                v___x_1382_ = leanh::lean_box(0);
                v___x_1383_ = lean_nat_dec_lt(v_u_1355_, v_size_1381_);
                if v___x_1383_ == 0 {
                    leanh::lean_dec_ref(v_targets_1380_);
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
                    leanh::lean_dec_ref(v_targets_1380_);
                    v___y_1375_ = v___x_1385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1376_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_1356_, v___y_1375_);
                leanh::lean_dec(v___y_1375_);
                if v_isShared_1373_ == 0 {
                    leanh::lean_ctor_set(v___x_1372_, 0, v___x_1376_);
                    v___x_1378_ = v___x_1372_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
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
                    v_reuseFailAlloc_1393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
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
    mut v_u_1395_: *mut leanh::LeanObject,
    mut v_v_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
    mut v_a_1404_: *mut leanh::LeanObject,
    mut v_a_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
    mut v_a_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1409_ = l_Lean_Meta_Grind_Order_getDist_x3f(
        v_u_1395_, v_v_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_,
        v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_,
    );
    leanh::lean_dec(v_a_1407_);
    leanh::lean_dec_ref(v_a_1406_);
    leanh::lean_dec(v_a_1405_);
    leanh::lean_dec_ref(v_a_1404_);
    leanh::lean_dec(v_a_1403_);
    leanh::lean_dec_ref(v_a_1402_);
    leanh::lean_dec(v_a_1401_);
    leanh::lean_dec_ref(v_a_1400_);
    leanh::lean_dec(v_a_1399_);
    leanh::lean_dec(v_a_1398_);
    leanh::lean_dec(v_a_1397_);
    leanh::lean_dec(v_v_1396_);
    leanh::lean_dec(v_u_1395_);
    return v_res_1409_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(
    mut v_00_u03b2_1410_: *mut leanh::LeanObject,
    mut v_a_1411_: *mut leanh::LeanObject,
    mut v_x_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ =
        l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
            v_a_1411_, v_x_1412_,
        );
    return v___x_1413_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___boxed(
    mut v_00_u03b2_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
    mut v_x_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(
        v_00_u03b2_1414_,
        v_a_1415_,
        v_x_1416_,
    );
    leanh::lean_dec(v_x_1416_);
    leanh::lean_dec(v_a_1415_);
    return v_res_1417_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getProof_x3f(
    mut v_u_1418_: *mut leanh::LeanObject,
    mut v_v_1419_: *mut leanh::LeanObject,
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
    mut v_a_1423_: *mut leanh::LeanObject,
    mut v_a_1424_: *mut leanh::LeanObject,
    mut v_a_1425_: *mut leanh::LeanObject,
    mut v_a_1426_: *mut leanh::LeanObject,
    mut v_a_1427_: *mut leanh::LeanObject,
    mut v_a_1428_: *mut leanh::LeanObject,
    mut v_a_1429_: *mut leanh::LeanObject,
    mut v_a_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1436_: u8 = 0;
    let mut v___y_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofs_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1449_: u8 = 0;
    let mut v_a_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1432_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_,
                    v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_,
                );
                if leanh::lean_obj_tag(v___x_1432_) == 0 {
                    v_a_1433_ = leanh::lean_ctor_get(v___x_1432_, 0);
                    v_isSharedCheck_1449_ = (!leanh::lean_is_exclusive(v___x_1432_)) as u8;
                    if v_isSharedCheck_1449_ == 0 {
                        v___x_1435_ = v___x_1432_;
                        v_isShared_1436_ = v_isSharedCheck_1449_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1433_);
                        leanh::lean_dec(v___x_1432_);
                        v___x_1435_ = leanh::lean_box(0);
                        v_isShared_1436_ = v_isSharedCheck_1449_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1450_ = leanh::lean_ctor_get(v___x_1432_, 0);
                    v_isSharedCheck_1457_ = (!leanh::lean_is_exclusive(v___x_1432_)) as u8;
                    if v_isSharedCheck_1457_ == 0 {
                        v___x_1452_ = v___x_1432_;
                        v_isShared_1453_ = v_isSharedCheck_1457_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1450_);
                        leanh::lean_dec(v___x_1432_);
                        v___x_1452_ = leanh::lean_box(0);
                        v_isShared_1453_ = v_isSharedCheck_1457_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_proofs_1443_ = leanh::lean_ctor_get(v_a_1433_, 20);
                leanh::lean_inc_ref(v_proofs_1443_);
                leanh::lean_dec(v_a_1433_);
                v_size_1444_ = leanh::lean_ctor_get(v_proofs_1443_, 2);
                v___x_1445_ = leanh::lean_box(0);
                v___x_1446_ = lean_nat_dec_lt(v_u_1418_, v_size_1444_);
                if v___x_1446_ == 0 {
                    leanh::lean_dec_ref(v_proofs_1443_);
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
                    leanh::lean_dec_ref(v_proofs_1443_);
                    v___y_1438_ = v___x_1448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1439_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_1419_, v___y_1438_);
                leanh::lean_dec(v___y_1438_);
                if v_isShared_1436_ == 0 {
                    leanh::lean_ctor_set(v___x_1435_, 0, v___x_1439_);
                    v___x_1441_ = v___x_1435_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
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
                    v_reuseFailAlloc_1456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
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
    mut v_u_1458_: *mut leanh::LeanObject,
    mut v_v_1459_: *mut leanh::LeanObject,
    mut v_a_1460_: *mut leanh::LeanObject,
    mut v_a_1461_: *mut leanh::LeanObject,
    mut v_a_1462_: *mut leanh::LeanObject,
    mut v_a_1463_: *mut leanh::LeanObject,
    mut v_a_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
    mut v_a_1470_: *mut leanh::LeanObject,
    mut v_a_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Lean_Meta_Grind_Order_getProof_x3f(
        v_u_1458_, v_v_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_,
        v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_,
    );
    leanh::lean_dec(v_a_1470_);
    leanh::lean_dec_ref(v_a_1469_);
    leanh::lean_dec(v_a_1468_);
    leanh::lean_dec_ref(v_a_1467_);
    leanh::lean_dec(v_a_1466_);
    leanh::lean_dec_ref(v_a_1465_);
    leanh::lean_dec(v_a_1464_);
    leanh::lean_dec_ref(v_a_1463_);
    leanh::lean_dec(v_a_1462_);
    leanh::lean_dec(v_a_1461_);
    leanh::lean_dec(v_a_1460_);
    leanh::lean_dec(v_v_1459_);
    leanh::lean_dec(v_u_1458_);
    return v_res_1472_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1473_: *mut leanh::LeanObject,
    mut v_vals_1474_: *mut leanh::LeanObject,
    mut v_i_1475_: *mut leanh::LeanObject,
    mut v_k_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_array_get_size(v_keys_1473_);
                v___x_1478_ = lean_nat_dec_lt(v_i_1475_, v___x_1477_);
                if v___x_1478_ == 0 {
                    leanh::lean_dec(v_i_1475_);
                    v___x_1479_ = leanh::lean_box(0);
                    return v___x_1479_;
                } else {
                    v_k_x27_1480_ = lean_array_fget_borrowed(v_keys_1473_, v_i_1475_);
                    v___x_1481_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1476_,
                            v_k_x27_1480_,
                        );
                    if v___x_1481_ == 0 {
                        v___x_1482_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1483_ = lean_nat_add(v_i_1475_, v___x_1482_);
                        leanh::lean_dec(v_i_1475_);
                        v_i_1475_ = v___x_1483_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1485_ = lean_array_fget_borrowed(v_vals_1474_, v_i_1475_);
                        leanh::lean_dec(v_i_1475_);
                        leanh::lean_inc(v___x_1485_);
                        v___x_1486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1486_, 0, v___x_1485_);
                        return v___x_1486_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1487_: *mut leanh::LeanObject,
    mut v_vals_1488_: *mut leanh::LeanObject,
    mut v_i_1489_: *mut leanh::LeanObject,
    mut v_k_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1491_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_1487_, v_vals_1488_, v_i_1489_, v_k_1490_);
    leanh::lean_dec_ref(v_k_1490_);
    leanh::lean_dec_ref(v_vals_1488_);
    leanh::lean_dec_ref(v_keys_1487_);
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
    v___x_1496_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0);
    v___x_1497_ = lean_usize_sub(v___x_1496_, v___x_1495_);
    return v___x_1497_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(
    mut v_x_1498_: *mut leanh::LeanObject,
    mut v_x_1499_: usize,
    mut v_x_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: usize = 0;
    let mut v___x_1505_: usize = 0;
    let mut v_j_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: usize = 0;
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1498_) == 0 {
                    v_es_1501_ = leanh::lean_ctor_get(v_x_1498_, 0);
                    v___x_1502_ = leanh::lean_box(2);
                    v___x_1503_ = 5usize;
                    v___x_1504_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1);
                    v___x_1505_ = lean_usize_land(v_x_1499_, v___x_1504_);
                    v_j_1506_ = lean_usize_to_nat(v___x_1505_);
                    v___x_1507_ = lean_array_get_borrowed(v___x_1502_, v_es_1501_, v_j_1506_);
                    leanh::lean_dec(v_j_1506_);
                    match leanh::lean_obj_tag(v___x_1507_) {
                        0 => {
                            v_key_1508_ = leanh::lean_ctor_get(v___x_1507_, 0);
                            v_val_1509_ = leanh::lean_ctor_get(v___x_1507_, 1);
                            v___x_1510_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1500_, v_key_1508_);
                            if v___x_1510_ == 0 {
                                v___x_1511_ = leanh::lean_box(0);
                                return v___x_1511_;
                            } else {
                                leanh::lean_inc(v_val_1509_);
                                v___x_1512_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1512_, 0, v_val_1509_);
                                return v___x_1512_;
                            }
                        }
                        1 => {
                            v_node_1513_ = leanh::lean_ctor_get(v___x_1507_, 0);
                            v___x_1514_ = lean_usize_shift_right(v_x_1499_, v___x_1503_);
                            v_x_1498_ = v_node_1513_;
                            v_x_1499_ = v___x_1514_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1516_ = leanh::lean_box(0);
                            return v___x_1516_;
                        }
                    }
                } else {
                    v_ks_1517_ = leanh::lean_ctor_get(v_x_1498_, 0);
                    v_vs_1518_ = leanh::lean_ctor_get(v_x_1498_, 1);
                    v___x_1519_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1520_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_ks_1517_, v_vs_1518_, v___x_1519_, v_x_1500_);
                    return v___x_1520_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___boxed(
    mut v_x_1521_: *mut leanh::LeanObject,
    mut v_x_1522_: *mut leanh::LeanObject,
    mut v_x_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1311__boxed_1524_: usize = 0;
    let mut v_res_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1311__boxed_1524_ = leanh::lean_unbox_usize(v_x_1522_);
    leanh::lean_dec(v_x_1522_);
    v_res_1525_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1521_, v_x_1311__boxed_1524_, v_x_1523_);
    leanh::lean_dec_ref(v_x_1523_);
    leanh::lean_dec_ref(v_x_1521_);
    return v_res_1525_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
    mut v_x_1526_: *mut leanh::LeanObject,
    mut v_x_1527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1528_: u64 = 0;
    let mut v___x_1529_: usize = 0;
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1527_);
    v___x_1529_ = lean_uint64_to_usize(v___x_1528_);
    v___x_1530_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1526_, v___x_1529_, v_x_1527_);
    return v___x_1530_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg___boxed(
    mut v_x_1531_: *mut leanh::LeanObject,
    mut v_x_1532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
            v_x_1531_, v_x_1532_,
        );
    leanh::lean_dec_ref(v_x_1532_);
    leanh::lean_dec_ref(v_x_1531_);
    return v_res_1533_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getNodeId___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = l_Lean_Meta_Grind_Order_getNodeId___closed__0;
    v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
    return v___x_1536_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getNodeId(
    mut v_e_1537_: *mut leanh::LeanObject,
    mut v_a_1538_: *mut leanh::LeanObject,
    mut v_a_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
    mut v_a_1541_: *mut leanh::LeanObject,
    mut v_a_1542_: *mut leanh::LeanObject,
    mut v_a_1543_: *mut leanh::LeanObject,
    mut v_a_1544_: *mut leanh::LeanObject,
    mut v_a_1545_: *mut leanh::LeanObject,
    mut v_a_1546_: *mut leanh::LeanObject,
    mut v_a_1547_: *mut leanh::LeanObject,
    mut v_a_1548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v_nodeMap_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut v_a_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1550_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_,
                    v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_,
                );
                if leanh::lean_obj_tag(v___x_1550_) == 0 {
                    v_a_1551_ = leanh::lean_ctor_get(v___x_1550_, 0);
                    v_isSharedCheck_1565_ = (!leanh::lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1565_ == 0 {
                        v___x_1553_ = v___x_1550_;
                        v_isShared_1554_ = v_isSharedCheck_1565_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1551_);
                        leanh::lean_dec(v___x_1550_);
                        v___x_1553_ = leanh::lean_box(0);
                        v_isShared_1554_ = v_isSharedCheck_1565_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1537_);
                    v_a_1566_ = leanh::lean_ctor_get(v___x_1550_, 0);
                    v_isSharedCheck_1573_ = (!leanh::lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v___x_1568_ = v___x_1550_;
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1566_);
                        leanh::lean_dec(v___x_1550_);
                        v___x_1568_ = leanh::lean_box(0);
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_nodeMap_1555_ = leanh::lean_ctor_get(v_a_1551_, 15);
                leanh::lean_inc_ref(v_nodeMap_1555_);
                leanh::lean_dec(v_a_1551_);
                v___x_1556_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_nodeMap_1555_, v_e_1537_);
                leanh::lean_dec_ref(v_nodeMap_1555_);
                if leanh::lean_obj_tag(v___x_1556_) == 1 {
                    leanh::lean_dec_ref(v_e_1537_);
                    v_val_1557_ = leanh::lean_ctor_get(v___x_1556_, 0);
                    leanh::lean_inc(v_val_1557_);
                    leanh::lean_dec_ref_known(v___x_1556_, 1);
                    if v_isShared_1554_ == 0 {
                        leanh::lean_ctor_set(v___x_1553_, 0, v_val_1557_);
                        v___x_1559_ = v___x_1553_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1560_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_val_1557_);
                        v___x_1559_ = v_reuseFailAlloc_1560_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1556_);
                    leanh::lean_del_object(v___x_1553_);
                    v___x_1561_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_getNodeId___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_getNodeId___closed__1_once),
                        _init_l_Lean_Meta_Grind_Order_getNodeId___closed__1,
                    );
                    v___x_1562_ = l_Lean_indentExpr(v_e_1537_);
                    v___x_1563_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1563_, 0, v___x_1561_);
                    leanh::lean_ctor_set(v___x_1563_, 1, v___x_1562_);
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
                    v_reuseFailAlloc_1572_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
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
    mut v_e_1574_: *mut leanh::LeanObject,
    mut v_a_1575_: *mut leanh::LeanObject,
    mut v_a_1576_: *mut leanh::LeanObject,
    mut v_a_1577_: *mut leanh::LeanObject,
    mut v_a_1578_: *mut leanh::LeanObject,
    mut v_a_1579_: *mut leanh::LeanObject,
    mut v_a_1580_: *mut leanh::LeanObject,
    mut v_a_1581_: *mut leanh::LeanObject,
    mut v_a_1582_: *mut leanh::LeanObject,
    mut v_a_1583_: *mut leanh::LeanObject,
    mut v_a_1584_: *mut leanh::LeanObject,
    mut v_a_1585_: *mut leanh::LeanObject,
    mut v_a_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1587_ = l_Lean_Meta_Grind_Order_getNodeId(
        v_e_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_,
        v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_,
    );
    leanh::lean_dec(v_a_1585_);
    leanh::lean_dec_ref(v_a_1584_);
    leanh::lean_dec(v_a_1583_);
    leanh::lean_dec_ref(v_a_1582_);
    leanh::lean_dec(v_a_1581_);
    leanh::lean_dec_ref(v_a_1580_);
    leanh::lean_dec(v_a_1579_);
    leanh::lean_dec_ref(v_a_1578_);
    leanh::lean_dec(v_a_1577_);
    leanh::lean_dec(v_a_1576_);
    leanh::lean_dec(v_a_1575_);
    return v_res_1587_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(
    mut v_00_u03b2_1588_: *mut leanh::LeanObject,
    mut v_x_1589_: *mut leanh::LeanObject,
    mut v_x_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
            v_x_1589_, v_x_1590_,
        );
    return v___x_1591_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___boxed(
    mut v_00_u03b2_1592_: *mut leanh::LeanObject,
    mut v_x_1593_: *mut leanh::LeanObject,
    mut v_x_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1595_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(
            v_00_u03b2_1592_,
            v_x_1593_,
            v_x_1594_,
        );
    leanh::lean_dec_ref(v_x_1594_);
    leanh::lean_dec_ref(v_x_1593_);
    return v_res_1595_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(
    mut v_00_u03b2_1596_: *mut leanh::LeanObject,
    mut v_x_1597_: *mut leanh::LeanObject,
    mut v_x_1598_: usize,
    mut v_x_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1597_, v_x_1598_, v_x_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___boxed(
    mut v_00_u03b2_1601_: *mut leanh::LeanObject,
    mut v_x_1602_: *mut leanh::LeanObject,
    mut v_x_1603_: *mut leanh::LeanObject,
    mut v_x_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1442__boxed_1605_: usize = 0;
    let mut v_res_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1442__boxed_1605_ = leanh::lean_unbox_usize(v_x_1603_);
    leanh::lean_dec(v_x_1603_);
    v_res_1606_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(v_00_u03b2_1601_, v_x_1602_, v_x_1442__boxed_1605_, v_x_1604_);
    leanh::lean_dec_ref(v_x_1604_);
    leanh::lean_dec_ref(v_x_1602_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1607_: *mut leanh::LeanObject,
    mut v_keys_1608_: *mut leanh::LeanObject,
    mut v_vals_1609_: *mut leanh::LeanObject,
    mut v_heq_1610_: *mut leanh::LeanObject,
    mut v_i_1611_: *mut leanh::LeanObject,
    mut v_k_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_1608_, v_vals_1609_, v_i_1611_, v_k_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1614_: *mut leanh::LeanObject,
    mut v_keys_1615_: *mut leanh::LeanObject,
    mut v_vals_1616_: *mut leanh::LeanObject,
    mut v_heq_1617_: *mut leanh::LeanObject,
    mut v_i_1618_: *mut leanh::LeanObject,
    mut v_k_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(v_00_u03b2_1614_, v_keys_1615_, v_vals_1616_, v_heq_1617_, v_i_1618_, v_k_1619_);
    leanh::lean_dec_ref(v_k_1619_);
    leanh::lean_dec_ref(v_vals_1616_);
    leanh::lean_dec_ref(v_keys_1615_);
    return v_res_1620_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getProof___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_Lean_Meta_Grind_Order_getProof___closed__0;
    v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getProof___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_Meta_Grind_Order_getProof___closed__2;
    v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
    return v___x_1626_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getProof(
    mut v_u_1627_: *mut leanh::LeanObject,
    mut v_v_1628_: *mut leanh::LeanObject,
    mut v_a_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
    mut v_a_1631_: *mut leanh::LeanObject,
    mut v_a_1632_: *mut leanh::LeanObject,
    mut v_a_1633_: *mut leanh::LeanObject,
    mut v_a_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
    mut v_a_1638_: *mut leanh::LeanObject,
    mut v_a_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v_val_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v_a_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1673_: u8 = 0;
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut v_isSharedCheck_1678_: u8 = 0;
    let mut v_a_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1641_ = l_Lean_Meta_Grind_Order_getProof_x3f(
                    v_u_1627_, v_v_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                    v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                );
                if leanh::lean_obj_tag(v___x_1641_) == 0 {
                    v_a_1642_ = leanh::lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1678_ = (!leanh::lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1678_ == 0 {
                        v___x_1644_ = v___x_1641_;
                        v_isShared_1645_ = v_isSharedCheck_1678_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1642_);
                        leanh::lean_dec(v___x_1641_);
                        v___x_1644_ = leanh::lean_box(0);
                        v_isShared_1645_ = v_isSharedCheck_1678_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1679_ = leanh::lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1686_ = (!leanh::lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1686_ == 0 {
                        v___x_1681_ = v___x_1641_;
                        v_isShared_1682_ = v_isSharedCheck_1686_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1679_);
                        leanh::lean_dec(v___x_1641_);
                        v___x_1681_ = leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1686_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1642_) == 1 {
                    v_val_1646_ = leanh::lean_ctor_get(v_a_1642_, 0);
                    leanh::lean_inc(v_val_1646_);
                    leanh::lean_dec_ref_known(v_a_1642_, 1);
                    if v_isShared_1645_ == 0 {
                        leanh::lean_ctor_set(v___x_1644_, 0, v_val_1646_);
                        v___x_1648_ = v___x_1644_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1646_);
                        v___x_1648_ = v_reuseFailAlloc_1649_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1644_);
                    leanh::lean_dec(v_a_1642_);
                    v___x_1650_ = l_Lean_Meta_Grind_Order_getExpr(
                        v_u_1627_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                        v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                    );
                    if leanh::lean_obj_tag(v___x_1650_) == 0 {
                        v_a_1651_ = leanh::lean_ctor_get(v___x_1650_, 0);
                        leanh::lean_inc(v_a_1651_);
                        leanh::lean_dec_ref_known(v___x_1650_, 1);
                        v___x_1652_ = l_Lean_Meta_Grind_Order_getExpr(
                            v_v_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                            v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                        );
                        if leanh::lean_obj_tag(v___x_1652_) == 0 {
                            v_a_1653_ = leanh::lean_ctor_get(v___x_1652_, 0);
                            leanh::lean_inc(v_a_1653_);
                            leanh::lean_dec_ref_known(v___x_1652_, 1);
                            v___x_1654_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__1_once
                                ),
                                _init_l_Lean_Meta_Grind_Order_getProof___closed__1,
                            );
                            v___x_1655_ = l_Lean_indentExpr(v_a_1651_);
                            v___x_1656_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1656_, 0, v___x_1654_);
                            leanh::lean_ctor_set(v___x_1656_, 1, v___x_1655_);
                            v___x_1657_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__3_once
                                ),
                                _init_l_Lean_Meta_Grind_Order_getProof___closed__3,
                            );
                            v___x_1658_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1658_, 0, v___x_1656_);
                            leanh::lean_ctor_set(v___x_1658_, 1, v___x_1657_);
                            v___x_1659_ = l_Lean_indentExpr(v_a_1653_);
                            v___x_1660_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1660_, 0, v___x_1658_);
                            leanh::lean_ctor_set(v___x_1660_, 1, v___x_1659_);
                            v___x_1661_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(v___x_1660_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
                            return v___x_1661_;
                        } else {
                            leanh::lean_dec(v_a_1651_);
                            v_a_1662_ = leanh::lean_ctor_get(v___x_1652_, 0);
                            v_isSharedCheck_1669_ =
                                (!leanh::lean_is_exclusive(v___x_1652_)) as u8;
                            if v_isSharedCheck_1669_ == 0 {
                                v___x_1664_ = v___x_1652_;
                                v_isShared_1665_ = v_isSharedCheck_1669_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1662_);
                                leanh::lean_dec(v___x_1652_);
                                v___x_1664_ = leanh::lean_box(0);
                                v_isShared_1665_ = v_isSharedCheck_1669_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_1670_ = leanh::lean_ctor_get(v___x_1650_, 0);
                        v_isSharedCheck_1677_ =
                            (!leanh::lean_is_exclusive(v___x_1650_)) as u8;
                        if v_isSharedCheck_1677_ == 0 {
                            v___x_1672_ = v___x_1650_;
                            v_isShared_1673_ = v_isSharedCheck_1677_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1670_);
                            leanh::lean_dec(v___x_1650_);
                            v___x_1672_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
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
                    v_reuseFailAlloc_1676_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
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
                    v_reuseFailAlloc_1685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
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
    mut v_u_1687_: *mut leanh::LeanObject,
    mut v_v_1688_: *mut leanh::LeanObject,
    mut v_a_1689_: *mut leanh::LeanObject,
    mut v_a_1690_: *mut leanh::LeanObject,
    mut v_a_1691_: *mut leanh::LeanObject,
    mut v_a_1692_: *mut leanh::LeanObject,
    mut v_a_1693_: *mut leanh::LeanObject,
    mut v_a_1694_: *mut leanh::LeanObject,
    mut v_a_1695_: *mut leanh::LeanObject,
    mut v_a_1696_: *mut leanh::LeanObject,
    mut v_a_1697_: *mut leanh::LeanObject,
    mut v_a_1698_: *mut leanh::LeanObject,
    mut v_a_1699_: *mut leanh::LeanObject,
    mut v_a_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lean_Meta_Grind_Order_getProof(
        v_u_1687_, v_v_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_,
        v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_,
    );
    leanh::lean_dec(v_a_1699_);
    leanh::lean_dec_ref(v_a_1698_);
    leanh::lean_dec(v_a_1697_);
    leanh::lean_dec_ref(v_a_1696_);
    leanh::lean_dec(v_a_1695_);
    leanh::lean_dec_ref(v_a_1694_);
    leanh::lean_dec(v_a_1693_);
    leanh::lean_dec_ref(v_a_1692_);
    leanh::lean_dec(v_a_1691_);
    leanh::lean_dec(v_a_1690_);
    leanh::lean_dec(v_a_1689_);
    leanh::lean_dec(v_v_1688_);
    leanh::lean_dec(v_u_1687_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getCnstr_x3f(
    mut v_e_1702_: *mut leanh::LeanObject,
    mut v_a_1703_: *mut leanh::LeanObject,
    mut v_a_1704_: *mut leanh::LeanObject,
    mut v_a_1705_: *mut leanh::LeanObject,
    mut v_a_1706_: *mut leanh::LeanObject,
    mut v_a_1707_: *mut leanh::LeanObject,
    mut v_a_1708_: *mut leanh::LeanObject,
    mut v_a_1709_: *mut leanh::LeanObject,
    mut v_a_1710_: *mut leanh::LeanObject,
    mut v_a_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
    mut v_a_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v_cnstrs_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1725_: u8 = 0;
    let mut v_a_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1715_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
                    v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_,
                );
                if leanh::lean_obj_tag(v___x_1715_) == 0 {
                    v_a_1716_ = leanh::lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1725_ = (!leanh::lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1725_ == 0 {
                        v___x_1718_ = v___x_1715_;
                        v_isShared_1719_ = v_isSharedCheck_1725_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1716_);
                        leanh::lean_dec(v___x_1715_);
                        v___x_1718_ = leanh::lean_box(0);
                        v_isShared_1719_ = v_isSharedCheck_1725_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1726_ = leanh::lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1733_ = (!leanh::lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1733_ == 0 {
                        v___x_1728_ = v___x_1715_;
                        v_isShared_1729_ = v_isSharedCheck_1733_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1726_);
                        leanh::lean_dec(v___x_1715_);
                        v___x_1728_ = leanh::lean_box(0);
                        v_isShared_1729_ = v_isSharedCheck_1733_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_cnstrs_1720_ = leanh::lean_ctor_get(v_a_1716_, 16);
                leanh::lean_inc_ref(v_cnstrs_1720_);
                leanh::lean_dec(v_a_1716_);
                v___x_1721_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_cnstrs_1720_, v_e_1702_);
                leanh::lean_dec_ref(v_cnstrs_1720_);
                if v_isShared_1719_ == 0 {
                    leanh::lean_ctor_set(v___x_1718_, 0, v___x_1721_);
                    v___x_1723_ = v___x_1718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
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
                    v_reuseFailAlloc_1732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
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
    mut v_e_1734_: *mut leanh::LeanObject,
    mut v_a_1735_: *mut leanh::LeanObject,
    mut v_a_1736_: *mut leanh::LeanObject,
    mut v_a_1737_: *mut leanh::LeanObject,
    mut v_a_1738_: *mut leanh::LeanObject,
    mut v_a_1739_: *mut leanh::LeanObject,
    mut v_a_1740_: *mut leanh::LeanObject,
    mut v_a_1741_: *mut leanh::LeanObject,
    mut v_a_1742_: *mut leanh::LeanObject,
    mut v_a_1743_: *mut leanh::LeanObject,
    mut v_a_1744_: *mut leanh::LeanObject,
    mut v_a_1745_: *mut leanh::LeanObject,
    mut v_a_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(
        v_e_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_,
        v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_,
    );
    leanh::lean_dec(v_a_1745_);
    leanh::lean_dec_ref(v_a_1744_);
    leanh::lean_dec(v_a_1743_);
    leanh::lean_dec_ref(v_a_1742_);
    leanh::lean_dec(v_a_1741_);
    leanh::lean_dec_ref(v_a_1740_);
    leanh::lean_dec(v_a_1739_);
    leanh::lean_dec_ref(v_a_1738_);
    leanh::lean_dec(v_a_1737_);
    leanh::lean_dec(v_a_1736_);
    leanh::lean_dec(v_a_1735_);
    leanh::lean_dec_ref(v_e_1734_);
    return v_res_1747_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isRing(
    mut v_a_1748_: *mut leanh::LeanObject,
    mut v_a_1749_: *mut leanh::LeanObject,
    mut v_a_1750_: *mut leanh::LeanObject,
    mut v_a_1751_: *mut leanh::LeanObject,
    mut v_a_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
    mut v_a_1754_: *mut leanh::LeanObject,
    mut v_a_1755_: *mut leanh::LeanObject,
    mut v_a_1756_: *mut leanh::LeanObject,
    mut v_a_1757_: *mut leanh::LeanObject,
    mut v_a_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v_ringId_x3f_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_a_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1760_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_,
                    v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_,
                );
                if leanh::lean_obj_tag(v___x_1760_) == 0 {
                    v_a_1761_ = leanh::lean_ctor_get(v___x_1760_, 0);
                    v_isSharedCheck_1776_ = (!leanh::lean_is_exclusive(v___x_1760_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v___x_1763_ = v___x_1760_;
                        v_isShared_1764_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1761_);
                        leanh::lean_dec(v___x_1760_);
                        v___x_1763_ = leanh::lean_box(0);
                        v_isShared_1764_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1777_ = leanh::lean_ctor_get(v___x_1760_, 0);
                    v_isSharedCheck_1784_ = (!leanh::lean_is_exclusive(v___x_1760_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1779_ = v___x_1760_;
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1777_);
                        leanh::lean_dec(v___x_1760_);
                        v___x_1779_ = leanh::lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_ringId_x3f_1765_ = leanh::lean_ctor_get(v_a_1761_, 9);
                leanh::lean_inc(v_ringId_x3f_1765_);
                leanh::lean_dec(v_a_1761_);
                if leanh::lean_obj_tag(v_ringId_x3f_1765_) == 0 {
                    v___x_1766_ = 0;
                    v___x_1767_ = leanh::lean_box((v___x_1766_) as usize);
                    if v_isShared_1764_ == 0 {
                        leanh::lean_ctor_set(v___x_1763_, 0, v___x_1767_);
                        v___x_1769_ = v___x_1763_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1770_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
                        v___x_1769_ = v_reuseFailAlloc_1770_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_ringId_x3f_1765_, 1);
                    v___x_1771_ = 1;
                    v___x_1772_ = leanh::lean_box((v___x_1771_) as usize);
                    if v_isShared_1764_ == 0 {
                        leanh::lean_ctor_set(v___x_1763_, 0, v___x_1772_);
                        v___x_1774_ = v___x_1763_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1775_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
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
                    v_reuseFailAlloc_1783_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
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
    mut v_a_1785_: *mut leanh::LeanObject,
    mut v_a_1786_: *mut leanh::LeanObject,
    mut v_a_1787_: *mut leanh::LeanObject,
    mut v_a_1788_: *mut leanh::LeanObject,
    mut v_a_1789_: *mut leanh::LeanObject,
    mut v_a_1790_: *mut leanh::LeanObject,
    mut v_a_1791_: *mut leanh::LeanObject,
    mut v_a_1792_: *mut leanh::LeanObject,
    mut v_a_1793_: *mut leanh::LeanObject,
    mut v_a_1794_: *mut leanh::LeanObject,
    mut v_a_1795_: *mut leanh::LeanObject,
    mut v_a_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1797_ = l_Lean_Meta_Grind_Order_isRing(
        v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_,
        v_a_1793_, v_a_1794_, v_a_1795_,
    );
    leanh::lean_dec(v_a_1795_);
    leanh::lean_dec_ref(v_a_1794_);
    leanh::lean_dec(v_a_1793_);
    leanh::lean_dec_ref(v_a_1792_);
    leanh::lean_dec(v_a_1791_);
    leanh::lean_dec_ref(v_a_1790_);
    leanh::lean_dec(v_a_1789_);
    leanh::lean_dec_ref(v_a_1788_);
    leanh::lean_dec(v_a_1787_);
    leanh::lean_dec(v_a_1786_);
    leanh::lean_dec(v_a_1785_);
    return v_res_1797_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isPartialOrder(
    mut v_a_1798_: *mut leanh::LeanObject,
    mut v_a_1799_: *mut leanh::LeanObject,
    mut v_a_1800_: *mut leanh::LeanObject,
    mut v_a_1801_: *mut leanh::LeanObject,
    mut v_a_1802_: *mut leanh::LeanObject,
    mut v_a_1803_: *mut leanh::LeanObject,
    mut v_a_1804_: *mut leanh::LeanObject,
    mut v_a_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
    mut v_a_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v_isPartialInst_x3f_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v_a_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1810_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_,
                    v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_,
                );
                if leanh::lean_obj_tag(v___x_1810_) == 0 {
                    v_a_1811_ = leanh::lean_ctor_get(v___x_1810_, 0);
                    v_isSharedCheck_1826_ = (!leanh::lean_is_exclusive(v___x_1810_)) as u8;
                    if v_isSharedCheck_1826_ == 0 {
                        v___x_1813_ = v___x_1810_;
                        v_isShared_1814_ = v_isSharedCheck_1826_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1811_);
                        leanh::lean_dec(v___x_1810_);
                        v___x_1813_ = leanh::lean_box(0);
                        v_isShared_1814_ = v_isSharedCheck_1826_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1827_ = leanh::lean_ctor_get(v___x_1810_, 0);
                    v_isSharedCheck_1834_ = (!leanh::lean_is_exclusive(v___x_1810_)) as u8;
                    if v_isSharedCheck_1834_ == 0 {
                        v___x_1829_ = v___x_1810_;
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1827_);
                        leanh::lean_dec(v___x_1810_);
                        v___x_1829_ = leanh::lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isPartialInst_x3f_1815_ = leanh::lean_ctor_get(v_a_1811_, 6);
                leanh::lean_inc(v_isPartialInst_x3f_1815_);
                leanh::lean_dec(v_a_1811_);
                if leanh::lean_obj_tag(v_isPartialInst_x3f_1815_) == 0 {
                    v___x_1816_ = 0;
                    v___x_1817_ = leanh::lean_box((v___x_1816_) as usize);
                    if v_isShared_1814_ == 0 {
                        leanh::lean_ctor_set(v___x_1813_, 0, v___x_1817_);
                        v___x_1819_ = v___x_1813_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1820_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                        v___x_1819_ = v_reuseFailAlloc_1820_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_isPartialInst_x3f_1815_, 1);
                    v___x_1821_ = 1;
                    v___x_1822_ = leanh::lean_box((v___x_1821_) as usize);
                    if v_isShared_1814_ == 0 {
                        leanh::lean_ctor_set(v___x_1813_, 0, v___x_1822_);
                        v___x_1824_ = v___x_1813_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
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
                    v_reuseFailAlloc_1833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
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
    mut v_a_1835_: *mut leanh::LeanObject,
    mut v_a_1836_: *mut leanh::LeanObject,
    mut v_a_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
    mut v_a_1839_: *mut leanh::LeanObject,
    mut v_a_1840_: *mut leanh::LeanObject,
    mut v_a_1841_: *mut leanh::LeanObject,
    mut v_a_1842_: *mut leanh::LeanObject,
    mut v_a_1843_: *mut leanh::LeanObject,
    mut v_a_1844_: *mut leanh::LeanObject,
    mut v_a_1845_: *mut leanh::LeanObject,
    mut v_a_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Lean_Meta_Grind_Order_isPartialOrder(
        v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_,
        v_a_1843_, v_a_1844_, v_a_1845_,
    );
    leanh::lean_dec(v_a_1845_);
    leanh::lean_dec_ref(v_a_1844_);
    leanh::lean_dec(v_a_1843_);
    leanh::lean_dec_ref(v_a_1842_);
    leanh::lean_dec(v_a_1841_);
    leanh::lean_dec_ref(v_a_1840_);
    leanh::lean_dec(v_a_1839_);
    leanh::lean_dec_ref(v_a_1838_);
    leanh::lean_dec(v_a_1837_);
    leanh::lean_dec(v_a_1836_);
    leanh::lean_dec(v_a_1835_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isLinearPreorder(
    mut v_a_1848_: *mut leanh::LeanObject,
    mut v_a_1849_: *mut leanh::LeanObject,
    mut v_a_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
    mut v_a_1852_: *mut leanh::LeanObject,
    mut v_a_1853_: *mut leanh::LeanObject,
    mut v_a_1854_: *mut leanh::LeanObject,
    mut v_a_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
    mut v_a_1857_: *mut leanh::LeanObject,
    mut v_a_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v_isLinearPreInst_x3f_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u8 = 0;
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u8 = 0;
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_a_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1860_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_,
                    v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_,
                );
                if leanh::lean_obj_tag(v___x_1860_) == 0 {
                    v_a_1861_ = leanh::lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1876_ = (!leanh::lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1876_ == 0 {
                        v___x_1863_ = v___x_1860_;
                        v_isShared_1864_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1861_);
                        leanh::lean_dec(v___x_1860_);
                        v___x_1863_ = leanh::lean_box(0);
                        v_isShared_1864_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1877_ = leanh::lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1884_ = (!leanh::lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1884_ == 0 {
                        v___x_1879_ = v___x_1860_;
                        v_isShared_1880_ = v_isSharedCheck_1884_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1877_);
                        leanh::lean_dec(v___x_1860_);
                        v___x_1879_ = leanh::lean_box(0);
                        v_isShared_1880_ = v_isSharedCheck_1884_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isLinearPreInst_x3f_1865_ = leanh::lean_ctor_get(v_a_1861_, 7);
                leanh::lean_inc(v_isLinearPreInst_x3f_1865_);
                leanh::lean_dec(v_a_1861_);
                if leanh::lean_obj_tag(v_isLinearPreInst_x3f_1865_) == 0 {
                    v___x_1866_ = 0;
                    v___x_1867_ = leanh::lean_box((v___x_1866_) as usize);
                    if v_isShared_1864_ == 0 {
                        leanh::lean_ctor_set(v___x_1863_, 0, v___x_1867_);
                        v___x_1869_ = v___x_1863_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
                        v___x_1869_ = v_reuseFailAlloc_1870_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_isLinearPreInst_x3f_1865_, 1);
                    v___x_1871_ = 1;
                    v___x_1872_ = leanh::lean_box((v___x_1871_) as usize);
                    if v_isShared_1864_ == 0 {
                        leanh::lean_ctor_set(v___x_1863_, 0, v___x_1872_);
                        v___x_1874_ = v___x_1863_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1875_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
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
                    v_reuseFailAlloc_1883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
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
    mut v_a_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
    mut v_a_1887_: *mut leanh::LeanObject,
    mut v_a_1888_: *mut leanh::LeanObject,
    mut v_a_1889_: *mut leanh::LeanObject,
    mut v_a_1890_: *mut leanh::LeanObject,
    mut v_a_1891_: *mut leanh::LeanObject,
    mut v_a_1892_: *mut leanh::LeanObject,
    mut v_a_1893_: *mut leanh::LeanObject,
    mut v_a_1894_: *mut leanh::LeanObject,
    mut v_a_1895_: *mut leanh::LeanObject,
    mut v_a_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lean_Meta_Grind_Order_isLinearPreorder(
        v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_,
        v_a_1893_, v_a_1894_, v_a_1895_,
    );
    leanh::lean_dec(v_a_1895_);
    leanh::lean_dec_ref(v_a_1894_);
    leanh::lean_dec(v_a_1893_);
    leanh::lean_dec_ref(v_a_1892_);
    leanh::lean_dec(v_a_1891_);
    leanh::lean_dec_ref(v_a_1890_);
    leanh::lean_dec(v_a_1889_);
    leanh::lean_dec_ref(v_a_1888_);
    leanh::lean_dec(v_a_1887_);
    leanh::lean_dec(v_a_1886_);
    leanh::lean_dec(v_a_1885_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_hasLt(
    mut v_a_1898_: *mut leanh::LeanObject,
    mut v_a_1899_: *mut leanh::LeanObject,
    mut v_a_1900_: *mut leanh::LeanObject,
    mut v_a_1901_: *mut leanh::LeanObject,
    mut v_a_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
    mut v_a_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
    mut v_a_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
    mut v_a_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v_lawfulOrderLTInst_x3f_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut v_a_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1910_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_,
                    v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_,
                );
                if leanh::lean_obj_tag(v___x_1910_) == 0 {
                    v_a_1911_ = leanh::lean_ctor_get(v___x_1910_, 0);
                    v_isSharedCheck_1926_ = (!leanh::lean_is_exclusive(v___x_1910_)) as u8;
                    if v_isSharedCheck_1926_ == 0 {
                        v___x_1913_ = v___x_1910_;
                        v_isShared_1914_ = v_isSharedCheck_1926_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1911_);
                        leanh::lean_dec(v___x_1910_);
                        v___x_1913_ = leanh::lean_box(0);
                        v_isShared_1914_ = v_isSharedCheck_1926_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1927_ = leanh::lean_ctor_get(v___x_1910_, 0);
                    v_isSharedCheck_1934_ = (!leanh::lean_is_exclusive(v___x_1910_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1929_ = v___x_1910_;
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1927_);
                        leanh::lean_dec(v___x_1910_);
                        v___x_1929_ = leanh::lean_box(0);
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_lawfulOrderLTInst_x3f_1915_ = leanh::lean_ctor_get(v_a_1911_, 8);
                leanh::lean_inc(v_lawfulOrderLTInst_x3f_1915_);
                leanh::lean_dec(v_a_1911_);
                if leanh::lean_obj_tag(v_lawfulOrderLTInst_x3f_1915_) == 0 {
                    v___x_1916_ = 0;
                    v___x_1917_ = leanh::lean_box((v___x_1916_) as usize);
                    if v_isShared_1914_ == 0 {
                        leanh::lean_ctor_set(v___x_1913_, 0, v___x_1917_);
                        v___x_1919_ = v___x_1913_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
                        v___x_1919_ = v_reuseFailAlloc_1920_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1915_, 1);
                    v___x_1921_ = 1;
                    v___x_1922_ = leanh::lean_box((v___x_1921_) as usize);
                    if v_isShared_1914_ == 0 {
                        leanh::lean_ctor_set(v___x_1913_, 0, v___x_1922_);
                        v___x_1924_ = v___x_1913_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1925_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
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
                    v_reuseFailAlloc_1933_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
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
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_a_1936_: *mut leanh::LeanObject,
    mut v_a_1937_: *mut leanh::LeanObject,
    mut v_a_1938_: *mut leanh::LeanObject,
    mut v_a_1939_: *mut leanh::LeanObject,
    mut v_a_1940_: *mut leanh::LeanObject,
    mut v_a_1941_: *mut leanh::LeanObject,
    mut v_a_1942_: *mut leanh::LeanObject,
    mut v_a_1943_: *mut leanh::LeanObject,
    mut v_a_1944_: *mut leanh::LeanObject,
    mut v_a_1945_: *mut leanh::LeanObject,
    mut v_a_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_Lean_Meta_Grind_Order_hasLt(
        v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_,
        v_a_1943_, v_a_1944_, v_a_1945_,
    );
    leanh::lean_dec(v_a_1945_);
    leanh::lean_dec_ref(v_a_1944_);
    leanh::lean_dec(v_a_1943_);
    leanh::lean_dec_ref(v_a_1942_);
    leanh::lean_dec(v_a_1941_);
    leanh::lean_dec_ref(v_a_1940_);
    leanh::lean_dec(v_a_1939_);
    leanh::lean_dec_ref(v_a_1938_);
    leanh::lean_dec(v_a_1937_);
    leanh::lean_dec(v_a_1936_);
    leanh::lean_dec(v_a_1935_);
    return v_res_1947_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isInt(
    mut v_a_1948_: *mut leanh::LeanObject,
    mut v_a_1949_: *mut leanh::LeanObject,
    mut v_a_1950_: *mut leanh::LeanObject,
    mut v_a_1951_: *mut leanh::LeanObject,
    mut v_a_1952_: *mut leanh::LeanObject,
    mut v_a_1953_: *mut leanh::LeanObject,
    mut v_a_1954_: *mut leanh::LeanObject,
    mut v_a_1955_: *mut leanh::LeanObject,
    mut v_a_1956_: *mut leanh::LeanObject,
    mut v_a_1957_: *mut leanh::LeanObject,
    mut v_a_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v_type_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v_a_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1981_: u8 = 0;
    let mut v_a_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1960_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_,
                    v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_,
                );
                if leanh::lean_obj_tag(v___x_1960_) == 0 {
                    v_a_1961_ = leanh::lean_ctor_get(v___x_1960_, 0);
                    leanh::lean_inc(v_a_1961_);
                    leanh::lean_dec_ref_known(v___x_1960_, 1);
                    v___x_1962_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_1953_);
                    if leanh::lean_obj_tag(v___x_1962_) == 0 {
                        v_a_1963_ = leanh::lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_1973_ =
                            (!leanh::lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_1973_ == 0 {
                            v___x_1965_ = v___x_1962_;
                            v_isShared_1966_ = v_isSharedCheck_1973_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1963_);
                            leanh::lean_dec(v___x_1962_);
                            v___x_1965_ = leanh::lean_box(0);
                            v_isShared_1966_ = v_isSharedCheck_1973_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1961_);
                        v_a_1974_ = leanh::lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_1981_ =
                            (!leanh::lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_1981_ == 0 {
                            v___x_1976_ = v___x_1962_;
                            v_isShared_1977_ = v_isSharedCheck_1981_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1974_);
                            leanh::lean_dec(v___x_1962_);
                            v___x_1976_ = leanh::lean_box(0);
                            v_isShared_1977_ = v_isSharedCheck_1981_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1982_ = leanh::lean_ctor_get(v___x_1960_, 0);
                    v_isSharedCheck_1989_ = (!leanh::lean_is_exclusive(v___x_1960_)) as u8;
                    if v_isSharedCheck_1989_ == 0 {
                        v___x_1984_ = v___x_1960_;
                        v_isShared_1985_ = v_isSharedCheck_1989_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1982_);
                        leanh::lean_dec(v___x_1960_);
                        v___x_1984_ = leanh::lean_box(0);
                        v_isShared_1985_ = v_isSharedCheck_1989_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_type_1967_ = leanh::lean_ctor_get(v_a_1961_, 1);
                leanh::lean_inc_ref(v_type_1967_);
                leanh::lean_dec(v_a_1961_);
                v___x_1968_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_1967_,
                        v_a_1963_,
                    );
                leanh::lean_dec(v_a_1963_);
                leanh::lean_dec_ref(v_type_1967_);
                v___x_1969_ = leanh::lean_box((v___x_1968_) as usize);
                if v_isShared_1966_ == 0 {
                    leanh::lean_ctor_set(v___x_1965_, 0, v___x_1969_);
                    v___x_1971_ = v___x_1965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
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
                    v_reuseFailAlloc_1980_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
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
                    v_reuseFailAlloc_1988_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
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
    mut v_a_1990_: *mut leanh::LeanObject,
    mut v_a_1991_: *mut leanh::LeanObject,
    mut v_a_1992_: *mut leanh::LeanObject,
    mut v_a_1993_: *mut leanh::LeanObject,
    mut v_a_1994_: *mut leanh::LeanObject,
    mut v_a_1995_: *mut leanh::LeanObject,
    mut v_a_1996_: *mut leanh::LeanObject,
    mut v_a_1997_: *mut leanh::LeanObject,
    mut v_a_1998_: *mut leanh::LeanObject,
    mut v_a_1999_: *mut leanh::LeanObject,
    mut v_a_2000_: *mut leanh::LeanObject,
    mut v_a_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_Meta_Grind_Order_isInt(
        v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_,
        v_a_1998_, v_a_1999_, v_a_2000_,
    );
    leanh::lean_dec(v_a_2000_);
    leanh::lean_dec_ref(v_a_1999_);
    leanh::lean_dec(v_a_1998_);
    leanh::lean_dec_ref(v_a_1997_);
    leanh::lean_dec(v_a_1996_);
    leanh::lean_dec_ref(v_a_1995_);
    leanh::lean_dec(v_a_1994_);
    leanh::lean_dec_ref(v_a_1993_);
    leanh::lean_dec(v_a_1992_);
    leanh::lean_dec(v_a_1991_);
    leanh::lean_dec(v_a_1990_);
    return v_res_2002_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_OrderM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
}