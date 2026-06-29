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
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{lean_usize_sub, lean_usize_to_nat};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::ffi::lean_st_ref_get;
pub static l_Lean_Meta_Grind_Order_getStruct___closed__0_value: crate::leanh::LeanStringObject<51> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_getStruct___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getStruct___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_getStruct___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_getStruct___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Grind_Order_getNodeId___closed__0_value: crate::leanh::LeanStringObject<71> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getNodeId___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_getNodeId___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_getProof___closed__0_value: crate::leanh::LeanStringObject<54> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_getProof___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_getProof___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_getProof___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_getProof___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_getProof___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_getProof___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_getProof___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_getProof___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___redArg(
    mut v_structId_1002_: *mut crate::leanh::LeanObject,
    mut v_x_1003_: *mut crate::leanh::LeanObject,
    mut v_a_1004_: *mut crate::leanh::LeanObject,
    mut v_a_1005_: *mut crate::leanh::LeanObject,
    mut v_a_1006_: *mut crate::leanh::LeanObject,
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_a_1009_: *mut crate::leanh::LeanObject,
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_a_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1013_);
    crate::leanh::lean_inc_ref(v_a_1012_);
    crate::leanh::lean_inc(v_a_1011_);
    crate::leanh::lean_inc_ref(v_a_1010_);
    crate::leanh::lean_inc(v_a_1009_);
    crate::leanh::lean_inc_ref(v_a_1008_);
    crate::leanh::lean_inc(v_a_1007_);
    crate::leanh::lean_inc_ref(v_a_1006_);
    crate::leanh::lean_inc(v_a_1005_);
    crate::leanh::lean_inc(v_a_1004_);
    v___x_1015_ = crate::leanh::lean_apply_12(
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
        crate::leanh::lean_box(0),
    );
    return v___x_1015_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___redArg___boxed(
    mut v_structId_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
    mut v_a_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
    mut v_a_1025_: *mut crate::leanh::LeanObject,
    mut v_a_1026_: *mut crate::leanh::LeanObject,
    mut v_a_1027_: *mut crate::leanh::LeanObject,
    mut v_a_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1027_);
    crate::leanh::lean_dec_ref(v_a_1026_);
    crate::leanh::lean_dec(v_a_1025_);
    crate::leanh::lean_dec_ref(v_a_1024_);
    crate::leanh::lean_dec(v_a_1023_);
    crate::leanh::lean_dec_ref(v_a_1022_);
    crate::leanh::lean_dec(v_a_1021_);
    crate::leanh::lean_dec_ref(v_a_1020_);
    crate::leanh::lean_dec(v_a_1019_);
    crate::leanh::lean_dec(v_a_1018_);
    return v_res_1029_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run(
    mut v_00_u03b1_1030_: *mut crate::leanh::LeanObject,
    mut v_structId_1031_: *mut crate::leanh::LeanObject,
    mut v_x_1032_: *mut crate::leanh::LeanObject,
    mut v_a_1033_: *mut crate::leanh::LeanObject,
    mut v_a_1034_: *mut crate::leanh::LeanObject,
    mut v_a_1035_: *mut crate::leanh::LeanObject,
    mut v_a_1036_: *mut crate::leanh::LeanObject,
    mut v_a_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
    mut v_a_1039_: *mut crate::leanh::LeanObject,
    mut v_a_1040_: *mut crate::leanh::LeanObject,
    mut v_a_1041_: *mut crate::leanh::LeanObject,
    mut v_a_1042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1042_);
    crate::leanh::lean_inc_ref(v_a_1041_);
    crate::leanh::lean_inc(v_a_1040_);
    crate::leanh::lean_inc_ref(v_a_1039_);
    crate::leanh::lean_inc(v_a_1038_);
    crate::leanh::lean_inc_ref(v_a_1037_);
    crate::leanh::lean_inc(v_a_1036_);
    crate::leanh::lean_inc_ref(v_a_1035_);
    crate::leanh::lean_inc(v_a_1034_);
    crate::leanh::lean_inc(v_a_1033_);
    v___x_1044_ = crate::leanh::lean_apply_12(
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
        crate::leanh::lean_box(0),
    );
    return v___x_1044_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_OrderM_run___boxed(
    mut v_00_u03b1_1045_: *mut crate::leanh::LeanObject,
    mut v_structId_1046_: *mut crate::leanh::LeanObject,
    mut v_x_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
    mut v_a_1050_: *mut crate::leanh::LeanObject,
    mut v_a_1051_: *mut crate::leanh::LeanObject,
    mut v_a_1052_: *mut crate::leanh::LeanObject,
    mut v_a_1053_: *mut crate::leanh::LeanObject,
    mut v_a_1054_: *mut crate::leanh::LeanObject,
    mut v_a_1055_: *mut crate::leanh::LeanObject,
    mut v_a_1056_: *mut crate::leanh::LeanObject,
    mut v_a_1057_: *mut crate::leanh::LeanObject,
    mut v_a_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1057_);
    crate::leanh::lean_dec_ref(v_a_1056_);
    crate::leanh::lean_dec(v_a_1055_);
    crate::leanh::lean_dec_ref(v_a_1054_);
    crate::leanh::lean_dec(v_a_1053_);
    crate::leanh::lean_dec_ref(v_a_1052_);
    crate::leanh::lean_dec(v_a_1051_);
    crate::leanh::lean_dec_ref(v_a_1050_);
    crate::leanh::lean_dec(v_a_1049_);
    crate::leanh::lean_dec(v_a_1048_);
    return v_res_1059_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___redArg(
    mut v_a_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1060_);
    v___x_1062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1062_, 0, v_a_1060_);
    return v___x_1062_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___redArg___boxed(
    mut v_a_1063_: *mut crate::leanh::LeanObject,
    mut v_a_1064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1065_ = l_Lean_Meta_Grind_Order_getStructId___redArg(v_a_1063_);
    crate::leanh::lean_dec(v_a_1063_);
    return v_res_1065_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId(
    mut v_a_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
    mut v_a_1068_: *mut crate::leanh::LeanObject,
    mut v_a_1069_: *mut crate::leanh::LeanObject,
    mut v_a_1070_: *mut crate::leanh::LeanObject,
    mut v_a_1071_: *mut crate::leanh::LeanObject,
    mut v_a_1072_: *mut crate::leanh::LeanObject,
    mut v_a_1073_: *mut crate::leanh::LeanObject,
    mut v_a_1074_: *mut crate::leanh::LeanObject,
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1066_);
    v___x_1078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1078_, 0, v_a_1066_);
    return v___x_1078_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId___boxed(
    mut v_a_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
    mut v_a_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_Lean_Meta_Grind_Order_getStructId(
        v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_,
        v_a_1087_, v_a_1088_, v_a_1089_,
    );
    crate::leanh::lean_dec(v_a_1089_);
    crate::leanh::lean_dec_ref(v_a_1088_);
    crate::leanh::lean_dec(v_a_1087_);
    crate::leanh::lean_dec_ref(v_a_1086_);
    crate::leanh::lean_dec(v_a_1085_);
    crate::leanh::lean_dec_ref(v_a_1084_);
    crate::leanh::lean_dec(v_a_1083_);
    crate::leanh::lean_dec_ref(v_a_1082_);
    crate::leanh::lean_dec(v_a_1081_);
    crate::leanh::lean_dec(v_a_1080_);
    crate::leanh::lean_dec(v_a_1079_);
    return v_res_1091_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(
    mut v_msgData_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = lean_st_ref_get(v___y_1096_);
    v_env_1099_ = crate::leanh::lean_ctor_get(v___x_1098_, 0);
    crate::leanh::lean_inc_ref(v_env_1099_);
    crate::leanh::lean_dec(v___x_1098_);
    v___x_1100_ = lean_st_ref_get(v___y_1094_);
    v_mctx_1101_ = crate::leanh::lean_ctor_get(v___x_1100_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1101_);
    crate::leanh::lean_dec(v___x_1100_);
    v_lctx_1102_ = crate::leanh::lean_ctor_get(v___y_1093_, 2);
    v_options_1103_ = crate::leanh::lean_ctor_get(v___y_1095_, 2);
    crate::leanh::lean_inc_ref(v_options_1103_);
    crate::leanh::lean_inc_ref(v_lctx_1102_);
    v___x_1104_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1104_, 0, v_env_1099_);
    crate::leanh::lean_ctor_set(v___x_1104_, 1, v_mctx_1101_);
    crate::leanh::lean_ctor_set(v___x_1104_, 2, v_lctx_1102_);
    crate::leanh::lean_ctor_set(v___x_1104_, 3, v_options_1103_);
    v___x_1105_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    crate::leanh::lean_ctor_set(v___x_1105_, 1, v_msgData_1092_);
    v___x_1106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1106_, 0, v___x_1105_);
    return v___x_1106_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0___boxed(
    mut v_msgData_1107_: *mut crate::leanh::LeanObject,
    mut v___y_1108_: *mut crate::leanh::LeanObject,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
    mut v___y_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(v_msgData_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
    crate::leanh::lean_dec(v___y_1111_);
    crate::leanh::lean_dec_ref(v___y_1110_);
    crate::leanh::lean_dec(v___y_1109_);
    crate::leanh::lean_dec_ref(v___y_1108_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
    mut v_msg_1114_: *mut crate::leanh::LeanObject,
    mut v___y_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
    mut v___y_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1125_: u8 = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1120_ = crate::leanh::lean_ctor_get(v___y_1117_, 5);
                v___x_1121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(v_msg_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
                v_a_1122_ = crate::leanh::lean_ctor_get(v___x_1121_, 0);
                v_isSharedCheck_1130_ = (!crate::leanh::lean_is_exclusive(v___x_1121_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v___x_1124_ = v___x_1121_;
                    v_isShared_1125_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1122_);
                    crate::leanh::lean_dec(v___x_1121_);
                    v___x_1124_ = crate::leanh::lean_box(0);
                    v_isShared_1125_ = v_isSharedCheck_1130_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1120_);
                v___x_1126_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1126_, 0, v_ref_1120_);
                crate::leanh::lean_ctor_set(v___x_1126_, 1, v_a_1122_);
                if v_isShared_1125_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1124_, 1);
                    crate::leanh::lean_ctor_set(v___x_1124_, 0, v___x_1126_);
                    v___x_1128_ = v___x_1124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
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
    mut v_msg_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(
        v_msg_1131_,
        v___y_1132_,
        v___y_1133_,
        v___y_1134_,
        v___y_1135_,
    );
    crate::leanh::lean_dec(v___y_1135_);
    crate::leanh::lean_dec_ref(v___y_1134_);
    crate::leanh::lean_dec(v___y_1133_);
    crate::leanh::lean_dec_ref(v___y_1132_);
    return v_res_1137_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getStruct___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1139_ = l_Lean_Meta_Grind_Order_getStruct___closed__0;
    v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
    return v___x_1140_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStruct(
    mut v_a_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
    mut v_a_1143_: *mut crate::leanh::LeanObject,
    mut v_a_1144_: *mut crate::leanh::LeanObject,
    mut v_a_1145_: *mut crate::leanh::LeanObject,
    mut v_a_1146_: *mut crate::leanh::LeanObject,
    mut v_a_1147_: *mut crate::leanh::LeanObject,
    mut v_a_1148_: *mut crate::leanh::LeanObject,
    mut v_a_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v_structs_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v_a_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1153_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1142_, v_a_1150_);
                if crate::leanh::lean_obj_tag(v___x_1153_) == 0 {
                    v_a_1154_ = crate::leanh::lean_ctor_get(v___x_1153_, 0);
                    v_isSharedCheck_1167_ = (!crate::leanh::lean_is_exclusive(v___x_1153_)) as u8;
                    if v_isSharedCheck_1167_ == 0 {
                        v___x_1156_ = v___x_1153_;
                        v_isShared_1157_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1154_);
                        crate::leanh::lean_dec(v___x_1153_);
                        v___x_1156_ = crate::leanh::lean_box(0);
                        v_isShared_1157_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1168_ = crate::leanh::lean_ctor_get(v___x_1153_, 0);
                    v_isSharedCheck_1175_ = (!crate::leanh::lean_is_exclusive(v___x_1153_)) as u8;
                    if v_isSharedCheck_1175_ == 0 {
                        v___x_1170_ = v___x_1153_;
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1168_);
                        crate::leanh::lean_dec(v___x_1153_);
                        v___x_1170_ = crate::leanh::lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1175_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_structs_1158_ = crate::leanh::lean_ctor_get(v_a_1154_, 0);
                crate::leanh::lean_inc_ref(v_structs_1158_);
                crate::leanh::lean_dec(v_a_1154_);
                v___x_1159_ = lean_array_get_size(v_structs_1158_);
                v___x_1160_ = lean_nat_dec_lt(v_a_1141_, v___x_1159_);
                if v___x_1160_ == 0 {
                    crate::leanh::lean_dec_ref(v_structs_1158_);
                    crate::leanh::lean_del_object(v___x_1156_);
                    v___x_1161_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec_ref(v_structs_1158_);
                    if v_isShared_1157_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1163_);
                        v___x_1165_ = v___x_1156_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
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
                    v_reuseFailAlloc_1174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
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
    mut v_a_1176_: *mut crate::leanh::LeanObject,
    mut v_a_1177_: *mut crate::leanh::LeanObject,
    mut v_a_1178_: *mut crate::leanh::LeanObject,
    mut v_a_1179_: *mut crate::leanh::LeanObject,
    mut v_a_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_a_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1188_ = l_Lean_Meta_Grind_Order_getStruct(
        v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_,
        v_a_1184_, v_a_1185_, v_a_1186_,
    );
    crate::leanh::lean_dec(v_a_1186_);
    crate::leanh::lean_dec_ref(v_a_1185_);
    crate::leanh::lean_dec(v_a_1184_);
    crate::leanh::lean_dec_ref(v_a_1183_);
    crate::leanh::lean_dec(v_a_1182_);
    crate::leanh::lean_dec_ref(v_a_1181_);
    crate::leanh::lean_dec(v_a_1180_);
    crate::leanh::lean_dec_ref(v_a_1179_);
    crate::leanh::lean_dec(v_a_1178_);
    crate::leanh::lean_dec(v_a_1177_);
    crate::leanh::lean_dec(v_a_1176_);
    return v_res_1188_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0(
    mut v_00_u03b1_1189_: *mut crate::leanh::LeanObject,
    mut v_msg_1190_: *mut crate::leanh::LeanObject,
    mut v___y_1191_: *mut crate::leanh::LeanObject,
    mut v___y_1192_: *mut crate::leanh::LeanObject,
    mut v___y_1193_: *mut crate::leanh::LeanObject,
    mut v___y_1194_: *mut crate::leanh::LeanObject,
    mut v___y_1195_: *mut crate::leanh::LeanObject,
    mut v___y_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
    mut v___y_1198_: *mut crate::leanh::LeanObject,
    mut v___y_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1204_: *mut crate::leanh::LeanObject,
    mut v_msg_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1216_);
    crate::leanh::lean_dec_ref(v___y_1215_);
    crate::leanh::lean_dec(v___y_1214_);
    crate::leanh::lean_dec_ref(v___y_1213_);
    crate::leanh::lean_dec(v___y_1212_);
    crate::leanh::lean_dec_ref(v___y_1211_);
    crate::leanh::lean_dec(v___y_1210_);
    crate::leanh::lean_dec_ref(v___y_1209_);
    crate::leanh::lean_dec(v___y_1208_);
    crate::leanh::lean_dec(v___y_1207_);
    crate::leanh::lean_dec(v___y_1206_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(
    mut v_a_1219_: *mut crate::leanh::LeanObject,
    mut v_f_1220_: *mut crate::leanh::LeanObject,
    mut v_s_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structs_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMap_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMapInv_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v_v_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_1222_ = crate::leanh::lean_ctor_get(v_s_1221_, 0);
                v_typeIdOf_1223_ = crate::leanh::lean_ctor_get(v_s_1221_, 1);
                v_exprToStructId_1224_ = crate::leanh::lean_ctor_get(v_s_1221_, 2);
                v_termMap_1225_ = crate::leanh::lean_ctor_get(v_s_1221_, 3);
                v_termMapInv_1226_ = crate::leanh::lean_ctor_get(v_s_1221_, 4);
                v___x_1227_ = lean_array_get_size(v_structs_1222_);
                v___x_1228_ = lean_nat_dec_lt(v_a_1219_, v___x_1227_);
                if v___x_1228_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_1220_);
                    return v_s_1221_;
                } else {
                    crate::leanh::lean_inc_ref(v_termMapInv_1226_);
                    crate::leanh::lean_inc_ref(v_termMap_1225_);
                    crate::leanh::lean_inc_ref(v_exprToStructId_1224_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_1223_);
                    crate::leanh::lean_inc_ref(v_structs_1222_);
                    v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v_s_1221_)) as u8;
                    if v_isSharedCheck_1240_ == 0 {
                        v_unused_1241_ = crate::leanh::lean_ctor_get(v_s_1221_, 4);
                        crate::leanh::lean_dec(v_unused_1241_);
                        v_unused_1242_ = crate::leanh::lean_ctor_get(v_s_1221_, 3);
                        crate::leanh::lean_dec(v_unused_1242_);
                        v_unused_1243_ = crate::leanh::lean_ctor_get(v_s_1221_, 2);
                        crate::leanh::lean_dec(v_unused_1243_);
                        v_unused_1244_ = crate::leanh::lean_ctor_get(v_s_1221_, 1);
                        crate::leanh::lean_dec(v_unused_1244_);
                        v_unused_1245_ = crate::leanh::lean_ctor_get(v_s_1221_, 0);
                        crate::leanh::lean_dec(v_unused_1245_);
                        v___x_1230_ = v_s_1221_;
                        v_isShared_1231_ = v_isSharedCheck_1240_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_1221_);
                        v___x_1230_ = crate::leanh::lean_box(0);
                        v_isShared_1231_ = v_isSharedCheck_1240_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1232_ = lean_array_fget(v_structs_1222_, v_a_1219_);
                v___x_1233_ = crate::leanh::lean_box(0);
                v_xs_x27_1234_ = lean_array_fset(v_structs_1222_, v_a_1219_, v___x_1233_);
                v___x_1235_ = crate::leanh::lean_apply_1(v_f_1220_, v_v_1232_);
                v___x_1236_ = lean_array_fset(v_xs_x27_1234_, v_a_1219_, v___x_1235_);
                if v_isShared_1231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1230_, 0, v___x_1236_);
                    v___x_1238_ = v___x_1230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_typeIdOf_1223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_exprToStructId_1224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_termMap_1225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_termMapInv_1226_);
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
    mut v_a_1246_: *mut crate::leanh::LeanObject,
    mut v_f_1247_: *mut crate::leanh::LeanObject,
    mut v_s_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ =
        l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(v_a_1246_, v_f_1247_, v_s_1248_);
    crate::leanh::lean_dec(v_a_1246_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg(
    mut v_f_1250_: *mut crate::leanh::LeanObject,
    mut v_a_1251_: *mut crate::leanh::LeanObject,
    mut v_a_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1251_);
    v___f_1254_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1254_, 0, v_a_1251_);
    crate::leanh::lean_closure_set(v___f_1254_, 1, v_f_1250_);
    v___x_1255_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_1256_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1255_, v___f_1254_, v_a_1252_);
    return v___x_1256_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___redArg___boxed(
    mut v_f_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_1257_, v_a_1258_, v_a_1259_);
    crate::leanh::lean_dec(v_a_1259_);
    crate::leanh::lean_dec(v_a_1258_);
    return v_res_1261_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct(
    mut v_f_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
    mut v_a_1265_: *mut crate::leanh::LeanObject,
    mut v_a_1266_: *mut crate::leanh::LeanObject,
    mut v_a_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_1262_, v_a_1263_, v_a_1264_);
    return v___x_1275_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modifyStruct___boxed(
    mut v_f_1276_: *mut crate::leanh::LeanObject,
    mut v_a_1277_: *mut crate::leanh::LeanObject,
    mut v_a_1278_: *mut crate::leanh::LeanObject,
    mut v_a_1279_: *mut crate::leanh::LeanObject,
    mut v_a_1280_: *mut crate::leanh::LeanObject,
    mut v_a_1281_: *mut crate::leanh::LeanObject,
    mut v_a_1282_: *mut crate::leanh::LeanObject,
    mut v_a_1283_: *mut crate::leanh::LeanObject,
    mut v_a_1284_: *mut crate::leanh::LeanObject,
    mut v_a_1285_: *mut crate::leanh::LeanObject,
    mut v_a_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Lean_Meta_Grind_Order_modifyStruct(
        v_f_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_,
        v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_,
    );
    crate::leanh::lean_dec(v_a_1287_);
    crate::leanh::lean_dec_ref(v_a_1286_);
    crate::leanh::lean_dec(v_a_1285_);
    crate::leanh::lean_dec_ref(v_a_1284_);
    crate::leanh::lean_dec(v_a_1283_);
    crate::leanh::lean_dec_ref(v_a_1282_);
    crate::leanh::lean_dec(v_a_1281_);
    crate::leanh::lean_dec_ref(v_a_1280_);
    crate::leanh::lean_dec(v_a_1279_);
    crate::leanh::lean_dec(v_a_1278_);
    crate::leanh::lean_dec(v_a_1277_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getExpr(
    mut v_u_1290_: *mut crate::leanh::LeanObject,
    mut v_a_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
    mut v_a_1297_: *mut crate::leanh::LeanObject,
    mut v_a_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v_nodes_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_a_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1303_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_,
                    v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_,
                );
                if crate::leanh::lean_obj_tag(v___x_1303_) == 0 {
                    v_a_1304_ = crate::leanh::lean_ctor_get(v___x_1303_, 0);
                    v_isSharedCheck_1320_ = (!crate::leanh::lean_is_exclusive(v___x_1303_)) as u8;
                    if v_isSharedCheck_1320_ == 0 {
                        v___x_1306_ = v___x_1303_;
                        v_isShared_1307_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1304_);
                        crate::leanh::lean_dec(v___x_1303_);
                        v___x_1306_ = crate::leanh::lean_box(0);
                        v_isShared_1307_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1321_ = crate::leanh::lean_ctor_get(v___x_1303_, 0);
                    v_isSharedCheck_1328_ = (!crate::leanh::lean_is_exclusive(v___x_1303_)) as u8;
                    if v_isSharedCheck_1328_ == 0 {
                        v___x_1323_ = v___x_1303_;
                        v_isShared_1324_ = v_isSharedCheck_1328_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1321_);
                        crate::leanh::lean_dec(v___x_1303_);
                        v___x_1323_ = crate::leanh::lean_box(0);
                        v_isShared_1324_ = v_isSharedCheck_1328_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_nodes_1308_ = crate::leanh::lean_ctor_get(v_a_1304_, 14);
                crate::leanh::lean_inc_ref(v_nodes_1308_);
                crate::leanh::lean_dec(v_a_1304_);
                v_size_1309_ = crate::leanh::lean_ctor_get(v_nodes_1308_, 2);
                v___x_1310_ = l_Lean_instInhabitedExpr;
                v___x_1311_ = lean_nat_dec_lt(v_u_1290_, v_size_1309_);
                if v___x_1311_ == 0 {
                    crate::leanh::lean_dec_ref(v_nodes_1308_);
                    v___x_1312_ = l_outOfBounds___redArg(v___x_1310_);
                    if v_isShared_1307_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1306_, 0, v___x_1312_);
                        v___x_1314_ = v___x_1306_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1315_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
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
                    crate::leanh::lean_dec_ref(v_nodes_1308_);
                    if v_isShared_1307_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1306_, 0, v___x_1316_);
                        v___x_1318_ = v___x_1306_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1319_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
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
                    v_reuseFailAlloc_1327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
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
    mut v_u_1329_: *mut crate::leanh::LeanObject,
    mut v_a_1330_: *mut crate::leanh::LeanObject,
    mut v_a_1331_: *mut crate::leanh::LeanObject,
    mut v_a_1332_: *mut crate::leanh::LeanObject,
    mut v_a_1333_: *mut crate::leanh::LeanObject,
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
    mut v_a_1337_: *mut crate::leanh::LeanObject,
    mut v_a_1338_: *mut crate::leanh::LeanObject,
    mut v_a_1339_: *mut crate::leanh::LeanObject,
    mut v_a_1340_: *mut crate::leanh::LeanObject,
    mut v_a_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_Lean_Meta_Grind_Order_getExpr(
        v_u_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_,
        v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_,
    );
    crate::leanh::lean_dec(v_a_1340_);
    crate::leanh::lean_dec_ref(v_a_1339_);
    crate::leanh::lean_dec(v_a_1338_);
    crate::leanh::lean_dec_ref(v_a_1337_);
    crate::leanh::lean_dec(v_a_1336_);
    crate::leanh::lean_dec_ref(v_a_1335_);
    crate::leanh::lean_dec(v_a_1334_);
    crate::leanh::lean_dec_ref(v_a_1333_);
    crate::leanh::lean_dec(v_a_1332_);
    crate::leanh::lean_dec(v_a_1331_);
    crate::leanh::lean_dec(v_a_1330_);
    crate::leanh::lean_dec(v_u_1329_);
    return v_res_1342_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
    mut v_a_1343_: *mut crate::leanh::LeanObject,
    mut v_x_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1344_) == 0 {
                    v___x_1345_ = crate::leanh::lean_box(0);
                    return v___x_1345_;
                } else {
                    v_key_1346_ = crate::leanh::lean_ctor_get(v_x_1344_, 0);
                    v_value_1347_ = crate::leanh::lean_ctor_get(v_x_1344_, 1);
                    v_tail_1348_ = crate::leanh::lean_ctor_get(v_x_1344_, 2);
                    v___x_1349_ = lean_nat_dec_eq(v_key_1346_, v_a_1343_);
                    if v___x_1349_ == 0 {
                        v_x_1344_ = v_tail_1348_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1347_);
                        v___x_1351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1351_, 0, v_value_1347_);
                        return v___x_1351_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg___boxed(
    mut v_a_1352_: *mut crate::leanh::LeanObject,
    mut v_x_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ =
        l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
            v_a_1352_, v_x_1353_,
        );
    crate::leanh::lean_dec(v_x_1353_);
    crate::leanh::lean_dec(v_a_1352_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getDist_x3f(
    mut v_u_1355_: *mut crate::leanh::LeanObject,
    mut v_v_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
    mut v_a_1364_: *mut crate::leanh::LeanObject,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v___y_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targets_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1386_: u8 = 0;
    let mut v_a_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1369_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_,
                    v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_,
                );
                if crate::leanh::lean_obj_tag(v___x_1369_) == 0 {
                    v_a_1370_ = crate::leanh::lean_ctor_get(v___x_1369_, 0);
                    v_isSharedCheck_1386_ = (!crate::leanh::lean_is_exclusive(v___x_1369_)) as u8;
                    if v_isSharedCheck_1386_ == 0 {
                        v___x_1372_ = v___x_1369_;
                        v_isShared_1373_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1370_);
                        crate::leanh::lean_dec(v___x_1369_);
                        v___x_1372_ = crate::leanh::lean_box(0);
                        v_isShared_1373_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1387_ = crate::leanh::lean_ctor_get(v___x_1369_, 0);
                    v_isSharedCheck_1394_ = (!crate::leanh::lean_is_exclusive(v___x_1369_)) as u8;
                    if v_isSharedCheck_1394_ == 0 {
                        v___x_1389_ = v___x_1369_;
                        v_isShared_1390_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1387_);
                        crate::leanh::lean_dec(v___x_1369_);
                        v___x_1389_ = crate::leanh::lean_box(0);
                        v_isShared_1390_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_targets_1380_ = crate::leanh::lean_ctor_get(v_a_1370_, 19);
                crate::leanh::lean_inc_ref(v_targets_1380_);
                crate::leanh::lean_dec(v_a_1370_);
                v_size_1381_ = crate::leanh::lean_ctor_get(v_targets_1380_, 2);
                v___x_1382_ = crate::leanh::lean_box(0);
                v___x_1383_ = lean_nat_dec_lt(v_u_1355_, v_size_1381_);
                if v___x_1383_ == 0 {
                    crate::leanh::lean_dec_ref(v_targets_1380_);
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
                    crate::leanh::lean_dec_ref(v_targets_1380_);
                    v___y_1375_ = v___x_1385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1376_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_1356_, v___y_1375_);
                crate::leanh::lean_dec(v___y_1375_);
                if v_isShared_1373_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1372_, 0, v___x_1376_);
                    v___x_1378_ = v___x_1372_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
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
                    v_reuseFailAlloc_1393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
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
    mut v_u_1395_: *mut crate::leanh::LeanObject,
    mut v_v_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1409_ = l_Lean_Meta_Grind_Order_getDist_x3f(
        v_u_1395_, v_v_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_,
        v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_,
    );
    crate::leanh::lean_dec(v_a_1407_);
    crate::leanh::lean_dec_ref(v_a_1406_);
    crate::leanh::lean_dec(v_a_1405_);
    crate::leanh::lean_dec_ref(v_a_1404_);
    crate::leanh::lean_dec(v_a_1403_);
    crate::leanh::lean_dec_ref(v_a_1402_);
    crate::leanh::lean_dec(v_a_1401_);
    crate::leanh::lean_dec_ref(v_a_1400_);
    crate::leanh::lean_dec(v_a_1399_);
    crate::leanh::lean_dec(v_a_1398_);
    crate::leanh::lean_dec(v_a_1397_);
    crate::leanh::lean_dec(v_v_1396_);
    crate::leanh::lean_dec(v_u_1395_);
    return v_res_1409_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(
    mut v_00_u03b2_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_x_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ =
        l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(
            v_a_1411_, v_x_1412_,
        );
    return v___x_1413_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___boxed(
    mut v_00_u03b2_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
    mut v_x_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(
        v_00_u03b2_1414_,
        v_a_1415_,
        v_x_1416_,
    );
    crate::leanh::lean_dec(v_x_1416_);
    crate::leanh::lean_dec(v_a_1415_);
    return v_res_1417_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getProof_x3f(
    mut v_u_1418_: *mut crate::leanh::LeanObject,
    mut v_v_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
    mut v_a_1425_: *mut crate::leanh::LeanObject,
    mut v_a_1426_: *mut crate::leanh::LeanObject,
    mut v_a_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
    mut v_a_1429_: *mut crate::leanh::LeanObject,
    mut v_a_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1436_: u8 = 0;
    let mut v___y_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofs_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1449_: u8 = 0;
    let mut v_a_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1432_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_,
                    v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_,
                );
                if crate::leanh::lean_obj_tag(v___x_1432_) == 0 {
                    v_a_1433_ = crate::leanh::lean_ctor_get(v___x_1432_, 0);
                    v_isSharedCheck_1449_ = (!crate::leanh::lean_is_exclusive(v___x_1432_)) as u8;
                    if v_isSharedCheck_1449_ == 0 {
                        v___x_1435_ = v___x_1432_;
                        v_isShared_1436_ = v_isSharedCheck_1449_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1433_);
                        crate::leanh::lean_dec(v___x_1432_);
                        v___x_1435_ = crate::leanh::lean_box(0);
                        v_isShared_1436_ = v_isSharedCheck_1449_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1450_ = crate::leanh::lean_ctor_get(v___x_1432_, 0);
                    v_isSharedCheck_1457_ = (!crate::leanh::lean_is_exclusive(v___x_1432_)) as u8;
                    if v_isSharedCheck_1457_ == 0 {
                        v___x_1452_ = v___x_1432_;
                        v_isShared_1453_ = v_isSharedCheck_1457_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1450_);
                        crate::leanh::lean_dec(v___x_1432_);
                        v___x_1452_ = crate::leanh::lean_box(0);
                        v_isShared_1453_ = v_isSharedCheck_1457_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_proofs_1443_ = crate::leanh::lean_ctor_get(v_a_1433_, 20);
                crate::leanh::lean_inc_ref(v_proofs_1443_);
                crate::leanh::lean_dec(v_a_1433_);
                v_size_1444_ = crate::leanh::lean_ctor_get(v_proofs_1443_, 2);
                v___x_1445_ = crate::leanh::lean_box(0);
                v___x_1446_ = lean_nat_dec_lt(v_u_1418_, v_size_1444_);
                if v___x_1446_ == 0 {
                    crate::leanh::lean_dec_ref(v_proofs_1443_);
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
                    crate::leanh::lean_dec_ref(v_proofs_1443_);
                    v___y_1438_ = v___x_1448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1439_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_1419_, v___y_1438_);
                crate::leanh::lean_dec(v___y_1438_);
                if v_isShared_1436_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1435_, 0, v___x_1439_);
                    v___x_1441_ = v___x_1435_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
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
                    v_reuseFailAlloc_1456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
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
    mut v_u_1458_: *mut crate::leanh::LeanObject,
    mut v_v_1459_: *mut crate::leanh::LeanObject,
    mut v_a_1460_: *mut crate::leanh::LeanObject,
    mut v_a_1461_: *mut crate::leanh::LeanObject,
    mut v_a_1462_: *mut crate::leanh::LeanObject,
    mut v_a_1463_: *mut crate::leanh::LeanObject,
    mut v_a_1464_: *mut crate::leanh::LeanObject,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
    mut v_a_1466_: *mut crate::leanh::LeanObject,
    mut v_a_1467_: *mut crate::leanh::LeanObject,
    mut v_a_1468_: *mut crate::leanh::LeanObject,
    mut v_a_1469_: *mut crate::leanh::LeanObject,
    mut v_a_1470_: *mut crate::leanh::LeanObject,
    mut v_a_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Lean_Meta_Grind_Order_getProof_x3f(
        v_u_1458_, v_v_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_,
        v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_,
    );
    crate::leanh::lean_dec(v_a_1470_);
    crate::leanh::lean_dec_ref(v_a_1469_);
    crate::leanh::lean_dec(v_a_1468_);
    crate::leanh::lean_dec_ref(v_a_1467_);
    crate::leanh::lean_dec(v_a_1466_);
    crate::leanh::lean_dec_ref(v_a_1465_);
    crate::leanh::lean_dec(v_a_1464_);
    crate::leanh::lean_dec_ref(v_a_1463_);
    crate::leanh::lean_dec(v_a_1462_);
    crate::leanh::lean_dec(v_a_1461_);
    crate::leanh::lean_dec(v_a_1460_);
    crate::leanh::lean_dec(v_v_1459_);
    crate::leanh::lean_dec(v_u_1458_);
    return v_res_1472_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1473_: *mut crate::leanh::LeanObject,
    mut v_vals_1474_: *mut crate::leanh::LeanObject,
    mut v_i_1475_: *mut crate::leanh::LeanObject,
    mut v_k_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_array_get_size(v_keys_1473_);
                v___x_1478_ = lean_nat_dec_lt(v_i_1475_, v___x_1477_);
                if v___x_1478_ == 0 {
                    crate::leanh::lean_dec(v_i_1475_);
                    v___x_1479_ = crate::leanh::lean_box(0);
                    return v___x_1479_;
                } else {
                    v_k_x27_1480_ = lean_array_fget_borrowed(v_keys_1473_, v_i_1475_);
                    v___x_1481_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1476_,
                            v_k_x27_1480_,
                        );
                    if v___x_1481_ == 0 {
                        v___x_1482_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1483_ = lean_nat_add(v_i_1475_, v___x_1482_);
                        crate::leanh::lean_dec(v_i_1475_);
                        v_i_1475_ = v___x_1483_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1485_ = lean_array_fget_borrowed(v_vals_1474_, v_i_1475_);
                        crate::leanh::lean_dec(v_i_1475_);
                        crate::leanh::lean_inc(v___x_1485_);
                        v___x_1486_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1486_, 0, v___x_1485_);
                        return v___x_1486_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1487_: *mut crate::leanh::LeanObject,
    mut v_vals_1488_: *mut crate::leanh::LeanObject,
    mut v_i_1489_: *mut crate::leanh::LeanObject,
    mut v_k_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1491_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_1487_, v_vals_1488_, v_i_1489_, v_k_1490_);
    crate::leanh::lean_dec_ref(v_k_1490_);
    crate::leanh::lean_dec_ref(v_vals_1488_);
    crate::leanh::lean_dec_ref(v_keys_1487_);
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
    v___x_1496_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__0);
    v___x_1497_ = lean_usize_sub(v___x_1496_, v___x_1495_);
    return v___x_1497_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(
    mut v_x_1498_: *mut crate::leanh::LeanObject,
    mut v_x_1499_: usize,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: usize = 0;
    let mut v___x_1505_: usize = 0;
    let mut v_j_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: usize = 0;
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1498_) == 0 {
                    v_es_1501_ = crate::leanh::lean_ctor_get(v_x_1498_, 0);
                    v___x_1502_ = crate::leanh::lean_box(2);
                    v___x_1503_ = 5usize;
                    v___x_1504_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___closed__1);
                    v___x_1505_ = lean_usize_land(v_x_1499_, v___x_1504_);
                    v_j_1506_ = lean_usize_to_nat(v___x_1505_);
                    v___x_1507_ = lean_array_get_borrowed(v___x_1502_, v_es_1501_, v_j_1506_);
                    crate::leanh::lean_dec(v_j_1506_);
                    match crate::leanh::lean_obj_tag(v___x_1507_) {
                        0 => {
                            v_key_1508_ = crate::leanh::lean_ctor_get(v___x_1507_, 0);
                            v_val_1509_ = crate::leanh::lean_ctor_get(v___x_1507_, 1);
                            v___x_1510_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1500_, v_key_1508_);
                            if v___x_1510_ == 0 {
                                v___x_1511_ = crate::leanh::lean_box(0);
                                return v___x_1511_;
                            } else {
                                crate::leanh::lean_inc(v_val_1509_);
                                v___x_1512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1512_, 0, v_val_1509_);
                                return v___x_1512_;
                            }
                        }
                        1 => {
                            v_node_1513_ = crate::leanh::lean_ctor_get(v___x_1507_, 0);
                            v___x_1514_ = lean_usize_shift_right(v_x_1499_, v___x_1503_);
                            v_x_1498_ = v_node_1513_;
                            v_x_1499_ = v___x_1514_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1516_ = crate::leanh::lean_box(0);
                            return v___x_1516_;
                        }
                    }
                } else {
                    v_ks_1517_ = crate::leanh::lean_ctor_get(v_x_1498_, 0);
                    v_vs_1518_ = crate::leanh::lean_ctor_get(v_x_1498_, 1);
                    v___x_1519_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1520_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_ks_1517_, v_vs_1518_, v___x_1519_, v_x_1500_);
                    return v___x_1520_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___boxed(
    mut v_x_1521_: *mut crate::leanh::LeanObject,
    mut v_x_1522_: *mut crate::leanh::LeanObject,
    mut v_x_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1311__boxed_1524_: usize = 0;
    let mut v_res_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1311__boxed_1524_ = crate::leanh::lean_unbox_usize(v_x_1522_);
    crate::leanh::lean_dec(v_x_1522_);
    v_res_1525_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1521_, v_x_1311__boxed_1524_, v_x_1523_);
    crate::leanh::lean_dec_ref(v_x_1523_);
    crate::leanh::lean_dec_ref(v_x_1521_);
    return v_res_1525_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
    mut v_x_1526_: *mut crate::leanh::LeanObject,
    mut v_x_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: u64 = 0;
    let mut v___x_1529_: usize = 0;
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1527_);
    v___x_1529_ = lean_uint64_to_usize(v___x_1528_);
    v___x_1530_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1526_, v___x_1529_, v_x_1527_);
    return v___x_1530_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg___boxed(
    mut v_x_1531_: *mut crate::leanh::LeanObject,
    mut v_x_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
            v_x_1531_, v_x_1532_,
        );
    crate::leanh::lean_dec_ref(v_x_1532_);
    crate::leanh::lean_dec_ref(v_x_1531_);
    return v_res_1533_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getNodeId___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = l_Lean_Meta_Grind_Order_getNodeId___closed__0;
    v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
    return v___x_1536_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getNodeId(
    mut v_e_1537_: *mut crate::leanh::LeanObject,
    mut v_a_1538_: *mut crate::leanh::LeanObject,
    mut v_a_1539_: *mut crate::leanh::LeanObject,
    mut v_a_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
    mut v_a_1542_: *mut crate::leanh::LeanObject,
    mut v_a_1543_: *mut crate::leanh::LeanObject,
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v_nodeMap_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut v_a_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1550_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_,
                    v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_,
                );
                if crate::leanh::lean_obj_tag(v___x_1550_) == 0 {
                    v_a_1551_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                    v_isSharedCheck_1565_ = (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1565_ == 0 {
                        v___x_1553_ = v___x_1550_;
                        v_isShared_1554_ = v_isSharedCheck_1565_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1551_);
                        crate::leanh::lean_dec(v___x_1550_);
                        v___x_1553_ = crate::leanh::lean_box(0);
                        v_isShared_1554_ = v_isSharedCheck_1565_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1537_);
                    v_a_1566_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                    v_isSharedCheck_1573_ = (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v___x_1568_ = v___x_1550_;
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1566_);
                        crate::leanh::lean_dec(v___x_1550_);
                        v___x_1568_ = crate::leanh::lean_box(0);
                        v_isShared_1569_ = v_isSharedCheck_1573_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_nodeMap_1555_ = crate::leanh::lean_ctor_get(v_a_1551_, 15);
                crate::leanh::lean_inc_ref(v_nodeMap_1555_);
                crate::leanh::lean_dec(v_a_1551_);
                v___x_1556_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_nodeMap_1555_, v_e_1537_);
                crate::leanh::lean_dec_ref(v_nodeMap_1555_);
                if crate::leanh::lean_obj_tag(v___x_1556_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_1537_);
                    v_val_1557_ = crate::leanh::lean_ctor_get(v___x_1556_, 0);
                    crate::leanh::lean_inc(v_val_1557_);
                    crate::leanh::lean_dec_ref_known(v___x_1556_, 1);
                    if v_isShared_1554_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1553_, 0, v_val_1557_);
                        v___x_1559_ = v___x_1553_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1560_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_val_1557_);
                        v___x_1559_ = v_reuseFailAlloc_1560_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1556_);
                    crate::leanh::lean_del_object(v___x_1553_);
                    v___x_1561_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_getNodeId___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_getNodeId___closed__1_once),
                        _init_l_Lean_Meta_Grind_Order_getNodeId___closed__1,
                    );
                    v___x_1562_ = l_Lean_indentExpr(v_e_1537_);
                    v___x_1563_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1563_, 0, v___x_1561_);
                    crate::leanh::lean_ctor_set(v___x_1563_, 1, v___x_1562_);
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
                    v_reuseFailAlloc_1572_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
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
    mut v_e_1574_: *mut crate::leanh::LeanObject,
    mut v_a_1575_: *mut crate::leanh::LeanObject,
    mut v_a_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
    mut v_a_1578_: *mut crate::leanh::LeanObject,
    mut v_a_1579_: *mut crate::leanh::LeanObject,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
    mut v_a_1581_: *mut crate::leanh::LeanObject,
    mut v_a_1582_: *mut crate::leanh::LeanObject,
    mut v_a_1583_: *mut crate::leanh::LeanObject,
    mut v_a_1584_: *mut crate::leanh::LeanObject,
    mut v_a_1585_: *mut crate::leanh::LeanObject,
    mut v_a_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1587_ = l_Lean_Meta_Grind_Order_getNodeId(
        v_e_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_,
        v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_,
    );
    crate::leanh::lean_dec(v_a_1585_);
    crate::leanh::lean_dec_ref(v_a_1584_);
    crate::leanh::lean_dec(v_a_1583_);
    crate::leanh::lean_dec_ref(v_a_1582_);
    crate::leanh::lean_dec(v_a_1581_);
    crate::leanh::lean_dec_ref(v_a_1580_);
    crate::leanh::lean_dec(v_a_1579_);
    crate::leanh::lean_dec_ref(v_a_1578_);
    crate::leanh::lean_dec(v_a_1577_);
    crate::leanh::lean_dec(v_a_1576_);
    crate::leanh::lean_dec(v_a_1575_);
    return v_res_1587_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(
    mut v_00_u03b2_1588_: *mut crate::leanh::LeanObject,
    mut v_x_1589_: *mut crate::leanh::LeanObject,
    mut v_x_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(
            v_x_1589_, v_x_1590_,
        );
    return v___x_1591_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___boxed(
    mut v_00_u03b2_1592_: *mut crate::leanh::LeanObject,
    mut v_x_1593_: *mut crate::leanh::LeanObject,
    mut v_x_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1595_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(
            v_00_u03b2_1592_,
            v_x_1593_,
            v_x_1594_,
        );
    crate::leanh::lean_dec_ref(v_x_1594_);
    crate::leanh::lean_dec_ref(v_x_1593_);
    return v_res_1595_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(
    mut v_00_u03b2_1596_: *mut crate::leanh::LeanObject,
    mut v_x_1597_: *mut crate::leanh::LeanObject,
    mut v_x_1598_: usize,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_1597_, v_x_1598_, v_x_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___boxed(
    mut v_00_u03b2_1601_: *mut crate::leanh::LeanObject,
    mut v_x_1602_: *mut crate::leanh::LeanObject,
    mut v_x_1603_: *mut crate::leanh::LeanObject,
    mut v_x_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1442__boxed_1605_: usize = 0;
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1442__boxed_1605_ = crate::leanh::lean_unbox_usize(v_x_1603_);
    crate::leanh::lean_dec(v_x_1603_);
    v_res_1606_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(v_00_u03b2_1601_, v_x_1602_, v_x_1442__boxed_1605_, v_x_1604_);
    crate::leanh::lean_dec_ref(v_x_1604_);
    crate::leanh::lean_dec_ref(v_x_1602_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1607_: *mut crate::leanh::LeanObject,
    mut v_keys_1608_: *mut crate::leanh::LeanObject,
    mut v_vals_1609_: *mut crate::leanh::LeanObject,
    mut v_heq_1610_: *mut crate::leanh::LeanObject,
    mut v_i_1611_: *mut crate::leanh::LeanObject,
    mut v_k_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_1608_, v_vals_1609_, v_i_1611_, v_k_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1614_: *mut crate::leanh::LeanObject,
    mut v_keys_1615_: *mut crate::leanh::LeanObject,
    mut v_vals_1616_: *mut crate::leanh::LeanObject,
    mut v_heq_1617_: *mut crate::leanh::LeanObject,
    mut v_i_1618_: *mut crate::leanh::LeanObject,
    mut v_k_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(v_00_u03b2_1614_, v_keys_1615_, v_vals_1616_, v_heq_1617_, v_i_1618_, v_k_1619_);
    crate::leanh::lean_dec_ref(v_k_1619_);
    crate::leanh::lean_dec_ref(v_vals_1616_);
    crate::leanh::lean_dec_ref(v_keys_1615_);
    return v_res_1620_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getProof___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_Lean_Meta_Grind_Order_getProof___closed__0;
    v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_getProof___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_Meta_Grind_Order_getProof___closed__2;
    v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
    return v___x_1626_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getProof(
    mut v_u_1627_: *mut crate::leanh::LeanObject,
    mut v_v_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
    mut v_a_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_a_1633_: *mut crate::leanh::LeanObject,
    mut v_a_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
    mut v_a_1637_: *mut crate::leanh::LeanObject,
    mut v_a_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v_val_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v_a_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1673_: u8 = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut v_isSharedCheck_1678_: u8 = 0;
    let mut v_a_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1641_ = l_Lean_Meta_Grind_Order_getProof_x3f(
                    v_u_1627_, v_v_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                    v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                );
                if crate::leanh::lean_obj_tag(v___x_1641_) == 0 {
                    v_a_1642_ = crate::leanh::lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1678_ = (!crate::leanh::lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1678_ == 0 {
                        v___x_1644_ = v___x_1641_;
                        v_isShared_1645_ = v_isSharedCheck_1678_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1642_);
                        crate::leanh::lean_dec(v___x_1641_);
                        v___x_1644_ = crate::leanh::lean_box(0);
                        v_isShared_1645_ = v_isSharedCheck_1678_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1679_ = crate::leanh::lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1686_ = (!crate::leanh::lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1686_ == 0 {
                        v___x_1681_ = v___x_1641_;
                        v_isShared_1682_ = v_isSharedCheck_1686_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1679_);
                        crate::leanh::lean_dec(v___x_1641_);
                        v___x_1681_ = crate::leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1686_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1642_) == 1 {
                    v_val_1646_ = crate::leanh::lean_ctor_get(v_a_1642_, 0);
                    crate::leanh::lean_inc(v_val_1646_);
                    crate::leanh::lean_dec_ref_known(v_a_1642_, 1);
                    if v_isShared_1645_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1644_, 0, v_val_1646_);
                        v___x_1648_ = v___x_1644_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1646_);
                        v___x_1648_ = v_reuseFailAlloc_1649_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1644_);
                    crate::leanh::lean_dec(v_a_1642_);
                    v___x_1650_ = l_Lean_Meta_Grind_Order_getExpr(
                        v_u_1627_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                        v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1650_) == 0 {
                        v_a_1651_ = crate::leanh::lean_ctor_get(v___x_1650_, 0);
                        crate::leanh::lean_inc(v_a_1651_);
                        crate::leanh::lean_dec_ref_known(v___x_1650_, 1);
                        v___x_1652_ = l_Lean_Meta_Grind_Order_getExpr(
                            v_v_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_,
                            v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1652_) == 0 {
                            v_a_1653_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                            crate::leanh::lean_inc(v_a_1653_);
                            crate::leanh::lean_dec_ref_known(v___x_1652_, 1);
                            v___x_1654_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__1_once
                                ),
                                _init_l_Lean_Meta_Grind_Order_getProof___closed__1,
                            );
                            v___x_1655_ = l_Lean_indentExpr(v_a_1651_);
                            v___x_1656_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1656_, 0, v___x_1654_);
                            crate::leanh::lean_ctor_set(v___x_1656_, 1, v___x_1655_);
                            v___x_1657_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Order_getProof___closed__3_once
                                ),
                                _init_l_Lean_Meta_Grind_Order_getProof___closed__3,
                            );
                            v___x_1658_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1658_, 0, v___x_1656_);
                            crate::leanh::lean_ctor_set(v___x_1658_, 1, v___x_1657_);
                            v___x_1659_ = l_Lean_indentExpr(v_a_1653_);
                            v___x_1660_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1660_, 0, v___x_1658_);
                            crate::leanh::lean_ctor_set(v___x_1660_, 1, v___x_1659_);
                            v___x_1661_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(v___x_1660_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
                            return v___x_1661_;
                        } else {
                            crate::leanh::lean_dec(v_a_1651_);
                            v_a_1662_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                            v_isSharedCheck_1669_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1652_)) as u8;
                            if v_isSharedCheck_1669_ == 0 {
                                v___x_1664_ = v___x_1652_;
                                v_isShared_1665_ = v_isSharedCheck_1669_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1662_);
                                crate::leanh::lean_dec(v___x_1652_);
                                v___x_1664_ = crate::leanh::lean_box(0);
                                v_isShared_1665_ = v_isSharedCheck_1669_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_1670_ = crate::leanh::lean_ctor_get(v___x_1650_, 0);
                        v_isSharedCheck_1677_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1650_)) as u8;
                        if v_isSharedCheck_1677_ == 0 {
                            v___x_1672_ = v___x_1650_;
                            v_isShared_1673_ = v_isSharedCheck_1677_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1670_);
                            crate::leanh::lean_dec(v___x_1650_);
                            v___x_1672_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
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
                    v_reuseFailAlloc_1676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
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
                    v_reuseFailAlloc_1685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
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
    mut v_u_1687_: *mut crate::leanh::LeanObject,
    mut v_v_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
    mut v_a_1692_: *mut crate::leanh::LeanObject,
    mut v_a_1693_: *mut crate::leanh::LeanObject,
    mut v_a_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
    mut v_a_1696_: *mut crate::leanh::LeanObject,
    mut v_a_1697_: *mut crate::leanh::LeanObject,
    mut v_a_1698_: *mut crate::leanh::LeanObject,
    mut v_a_1699_: *mut crate::leanh::LeanObject,
    mut v_a_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lean_Meta_Grind_Order_getProof(
        v_u_1687_, v_v_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_,
        v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_,
    );
    crate::leanh::lean_dec(v_a_1699_);
    crate::leanh::lean_dec_ref(v_a_1698_);
    crate::leanh::lean_dec(v_a_1697_);
    crate::leanh::lean_dec_ref(v_a_1696_);
    crate::leanh::lean_dec(v_a_1695_);
    crate::leanh::lean_dec_ref(v_a_1694_);
    crate::leanh::lean_dec(v_a_1693_);
    crate::leanh::lean_dec_ref(v_a_1692_);
    crate::leanh::lean_dec(v_a_1691_);
    crate::leanh::lean_dec(v_a_1690_);
    crate::leanh::lean_dec(v_a_1689_);
    crate::leanh::lean_dec(v_v_1688_);
    crate::leanh::lean_dec(v_u_1687_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getCnstr_x3f(
    mut v_e_1702_: *mut crate::leanh::LeanObject,
    mut v_a_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
    mut v_a_1710_: *mut crate::leanh::LeanObject,
    mut v_a_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v_cnstrs_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1725_: u8 = 0;
    let mut v_a_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1715_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
                    v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_,
                );
                if crate::leanh::lean_obj_tag(v___x_1715_) == 0 {
                    v_a_1716_ = crate::leanh::lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1725_ = (!crate::leanh::lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1725_ == 0 {
                        v___x_1718_ = v___x_1715_;
                        v_isShared_1719_ = v_isSharedCheck_1725_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1716_);
                        crate::leanh::lean_dec(v___x_1715_);
                        v___x_1718_ = crate::leanh::lean_box(0);
                        v_isShared_1719_ = v_isSharedCheck_1725_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1726_ = crate::leanh::lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1733_ = (!crate::leanh::lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1733_ == 0 {
                        v___x_1728_ = v___x_1715_;
                        v_isShared_1729_ = v_isSharedCheck_1733_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1726_);
                        crate::leanh::lean_dec(v___x_1715_);
                        v___x_1728_ = crate::leanh::lean_box(0);
                        v_isShared_1729_ = v_isSharedCheck_1733_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_cnstrs_1720_ = crate::leanh::lean_ctor_get(v_a_1716_, 16);
                crate::leanh::lean_inc_ref(v_cnstrs_1720_);
                crate::leanh::lean_dec(v_a_1716_);
                v___x_1721_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_cnstrs_1720_, v_e_1702_);
                crate::leanh::lean_dec_ref(v_cnstrs_1720_);
                if v_isShared_1719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1721_);
                    v___x_1723_ = v___x_1718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
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
                    v_reuseFailAlloc_1732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
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
    mut v_e_1734_: *mut crate::leanh::LeanObject,
    mut v_a_1735_: *mut crate::leanh::LeanObject,
    mut v_a_1736_: *mut crate::leanh::LeanObject,
    mut v_a_1737_: *mut crate::leanh::LeanObject,
    mut v_a_1738_: *mut crate::leanh::LeanObject,
    mut v_a_1739_: *mut crate::leanh::LeanObject,
    mut v_a_1740_: *mut crate::leanh::LeanObject,
    mut v_a_1741_: *mut crate::leanh::LeanObject,
    mut v_a_1742_: *mut crate::leanh::LeanObject,
    mut v_a_1743_: *mut crate::leanh::LeanObject,
    mut v_a_1744_: *mut crate::leanh::LeanObject,
    mut v_a_1745_: *mut crate::leanh::LeanObject,
    mut v_a_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(
        v_e_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_,
        v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_,
    );
    crate::leanh::lean_dec(v_a_1745_);
    crate::leanh::lean_dec_ref(v_a_1744_);
    crate::leanh::lean_dec(v_a_1743_);
    crate::leanh::lean_dec_ref(v_a_1742_);
    crate::leanh::lean_dec(v_a_1741_);
    crate::leanh::lean_dec_ref(v_a_1740_);
    crate::leanh::lean_dec(v_a_1739_);
    crate::leanh::lean_dec_ref(v_a_1738_);
    crate::leanh::lean_dec(v_a_1737_);
    crate::leanh::lean_dec(v_a_1736_);
    crate::leanh::lean_dec(v_a_1735_);
    crate::leanh::lean_dec_ref(v_e_1734_);
    return v_res_1747_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isRing(
    mut v_a_1748_: *mut crate::leanh::LeanObject,
    mut v_a_1749_: *mut crate::leanh::LeanObject,
    mut v_a_1750_: *mut crate::leanh::LeanObject,
    mut v_a_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
    mut v_a_1754_: *mut crate::leanh::LeanObject,
    mut v_a_1755_: *mut crate::leanh::LeanObject,
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v_ringId_x3f_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_a_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1760_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_,
                    v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_,
                );
                if crate::leanh::lean_obj_tag(v___x_1760_) == 0 {
                    v_a_1761_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
                    v_isSharedCheck_1776_ = (!crate::leanh::lean_is_exclusive(v___x_1760_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v___x_1763_ = v___x_1760_;
                        v_isShared_1764_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1761_);
                        crate::leanh::lean_dec(v___x_1760_);
                        v___x_1763_ = crate::leanh::lean_box(0);
                        v_isShared_1764_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1777_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
                    v_isSharedCheck_1784_ = (!crate::leanh::lean_is_exclusive(v___x_1760_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1779_ = v___x_1760_;
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1777_);
                        crate::leanh::lean_dec(v___x_1760_);
                        v___x_1779_ = crate::leanh::lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_ringId_x3f_1765_ = crate::leanh::lean_ctor_get(v_a_1761_, 9);
                crate::leanh::lean_inc(v_ringId_x3f_1765_);
                crate::leanh::lean_dec(v_a_1761_);
                if crate::leanh::lean_obj_tag(v_ringId_x3f_1765_) == 0 {
                    v___x_1766_ = 0;
                    v___x_1767_ = crate::leanh::lean_box((v___x_1766_) as usize);
                    if v_isShared_1764_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1763_, 0, v___x_1767_);
                        v___x_1769_ = v___x_1763_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
                        v___x_1769_ = v_reuseFailAlloc_1770_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_ringId_x3f_1765_, 1);
                    v___x_1771_ = 1;
                    v___x_1772_ = crate::leanh::lean_box((v___x_1771_) as usize);
                    if v_isShared_1764_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1763_, 0, v___x_1772_);
                        v___x_1774_ = v___x_1763_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
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
                    v_reuseFailAlloc_1783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
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
    mut v_a_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
    mut v_a_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
    mut v_a_1791_: *mut crate::leanh::LeanObject,
    mut v_a_1792_: *mut crate::leanh::LeanObject,
    mut v_a_1793_: *mut crate::leanh::LeanObject,
    mut v_a_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1797_ = l_Lean_Meta_Grind_Order_isRing(
        v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_,
        v_a_1793_, v_a_1794_, v_a_1795_,
    );
    crate::leanh::lean_dec(v_a_1795_);
    crate::leanh::lean_dec_ref(v_a_1794_);
    crate::leanh::lean_dec(v_a_1793_);
    crate::leanh::lean_dec_ref(v_a_1792_);
    crate::leanh::lean_dec(v_a_1791_);
    crate::leanh::lean_dec_ref(v_a_1790_);
    crate::leanh::lean_dec(v_a_1789_);
    crate::leanh::lean_dec_ref(v_a_1788_);
    crate::leanh::lean_dec(v_a_1787_);
    crate::leanh::lean_dec(v_a_1786_);
    crate::leanh::lean_dec(v_a_1785_);
    return v_res_1797_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isPartialOrder(
    mut v_a_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
    mut v_a_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
    mut v_a_1802_: *mut crate::leanh::LeanObject,
    mut v_a_1803_: *mut crate::leanh::LeanObject,
    mut v_a_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v_isPartialInst_x3f_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v_a_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1810_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_,
                    v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_,
                );
                if crate::leanh::lean_obj_tag(v___x_1810_) == 0 {
                    v_a_1811_ = crate::leanh::lean_ctor_get(v___x_1810_, 0);
                    v_isSharedCheck_1826_ = (!crate::leanh::lean_is_exclusive(v___x_1810_)) as u8;
                    if v_isSharedCheck_1826_ == 0 {
                        v___x_1813_ = v___x_1810_;
                        v_isShared_1814_ = v_isSharedCheck_1826_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1811_);
                        crate::leanh::lean_dec(v___x_1810_);
                        v___x_1813_ = crate::leanh::lean_box(0);
                        v_isShared_1814_ = v_isSharedCheck_1826_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1827_ = crate::leanh::lean_ctor_get(v___x_1810_, 0);
                    v_isSharedCheck_1834_ = (!crate::leanh::lean_is_exclusive(v___x_1810_)) as u8;
                    if v_isSharedCheck_1834_ == 0 {
                        v___x_1829_ = v___x_1810_;
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1827_);
                        crate::leanh::lean_dec(v___x_1810_);
                        v___x_1829_ = crate::leanh::lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isPartialInst_x3f_1815_ = crate::leanh::lean_ctor_get(v_a_1811_, 6);
                crate::leanh::lean_inc(v_isPartialInst_x3f_1815_);
                crate::leanh::lean_dec(v_a_1811_);
                if crate::leanh::lean_obj_tag(v_isPartialInst_x3f_1815_) == 0 {
                    v___x_1816_ = 0;
                    v___x_1817_ = crate::leanh::lean_box((v___x_1816_) as usize);
                    if v_isShared_1814_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1817_);
                        v___x_1819_ = v___x_1813_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                        v___x_1819_ = v_reuseFailAlloc_1820_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_isPartialInst_x3f_1815_, 1);
                    v___x_1821_ = 1;
                    v___x_1822_ = crate::leanh::lean_box((v___x_1821_) as usize);
                    if v_isShared_1814_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1822_);
                        v___x_1824_ = v___x_1813_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
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
                    v_reuseFailAlloc_1833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
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
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
    mut v_a_1842_: *mut crate::leanh::LeanObject,
    mut v_a_1843_: *mut crate::leanh::LeanObject,
    mut v_a_1844_: *mut crate::leanh::LeanObject,
    mut v_a_1845_: *mut crate::leanh::LeanObject,
    mut v_a_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Lean_Meta_Grind_Order_isPartialOrder(
        v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_,
        v_a_1843_, v_a_1844_, v_a_1845_,
    );
    crate::leanh::lean_dec(v_a_1845_);
    crate::leanh::lean_dec_ref(v_a_1844_);
    crate::leanh::lean_dec(v_a_1843_);
    crate::leanh::lean_dec_ref(v_a_1842_);
    crate::leanh::lean_dec(v_a_1841_);
    crate::leanh::lean_dec_ref(v_a_1840_);
    crate::leanh::lean_dec(v_a_1839_);
    crate::leanh::lean_dec_ref(v_a_1838_);
    crate::leanh::lean_dec(v_a_1837_);
    crate::leanh::lean_dec(v_a_1836_);
    crate::leanh::lean_dec(v_a_1835_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isLinearPreorder(
    mut v_a_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
    mut v_a_1850_: *mut crate::leanh::LeanObject,
    mut v_a_1851_: *mut crate::leanh::LeanObject,
    mut v_a_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
    mut v_a_1855_: *mut crate::leanh::LeanObject,
    mut v_a_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_a_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v_isLinearPreInst_x3f_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u8 = 0;
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u8 = 0;
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_a_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1860_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_,
                    v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_,
                );
                if crate::leanh::lean_obj_tag(v___x_1860_) == 0 {
                    v_a_1861_ = crate::leanh::lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1876_ = (!crate::leanh::lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1876_ == 0 {
                        v___x_1863_ = v___x_1860_;
                        v_isShared_1864_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1861_);
                        crate::leanh::lean_dec(v___x_1860_);
                        v___x_1863_ = crate::leanh::lean_box(0);
                        v_isShared_1864_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1877_ = crate::leanh::lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1884_ = (!crate::leanh::lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1884_ == 0 {
                        v___x_1879_ = v___x_1860_;
                        v_isShared_1880_ = v_isSharedCheck_1884_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1877_);
                        crate::leanh::lean_dec(v___x_1860_);
                        v___x_1879_ = crate::leanh::lean_box(0);
                        v_isShared_1880_ = v_isSharedCheck_1884_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isLinearPreInst_x3f_1865_ = crate::leanh::lean_ctor_get(v_a_1861_, 7);
                crate::leanh::lean_inc(v_isLinearPreInst_x3f_1865_);
                crate::leanh::lean_dec(v_a_1861_);
                if crate::leanh::lean_obj_tag(v_isLinearPreInst_x3f_1865_) == 0 {
                    v___x_1866_ = 0;
                    v___x_1867_ = crate::leanh::lean_box((v___x_1866_) as usize);
                    if v_isShared_1864_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1867_);
                        v___x_1869_ = v___x_1863_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
                        v___x_1869_ = v_reuseFailAlloc_1870_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_isLinearPreInst_x3f_1865_, 1);
                    v___x_1871_ = 1;
                    v___x_1872_ = crate::leanh::lean_box((v___x_1871_) as usize);
                    if v_isShared_1864_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1872_);
                        v___x_1874_ = v___x_1863_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
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
                    v_reuseFailAlloc_1883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
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
    mut v_a_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
    mut v_a_1891_: *mut crate::leanh::LeanObject,
    mut v_a_1892_: *mut crate::leanh::LeanObject,
    mut v_a_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lean_Meta_Grind_Order_isLinearPreorder(
        v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_,
        v_a_1893_, v_a_1894_, v_a_1895_,
    );
    crate::leanh::lean_dec(v_a_1895_);
    crate::leanh::lean_dec_ref(v_a_1894_);
    crate::leanh::lean_dec(v_a_1893_);
    crate::leanh::lean_dec_ref(v_a_1892_);
    crate::leanh::lean_dec(v_a_1891_);
    crate::leanh::lean_dec_ref(v_a_1890_);
    crate::leanh::lean_dec(v_a_1889_);
    crate::leanh::lean_dec_ref(v_a_1888_);
    crate::leanh::lean_dec(v_a_1887_);
    crate::leanh::lean_dec(v_a_1886_);
    crate::leanh::lean_dec(v_a_1885_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_hasLt(
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
    mut v_a_1901_: *mut crate::leanh::LeanObject,
    mut v_a_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
    mut v_a_1904_: *mut crate::leanh::LeanObject,
    mut v_a_1905_: *mut crate::leanh::LeanObject,
    mut v_a_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
    mut v_a_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v_lawfulOrderLTInst_x3f_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut v_a_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1910_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_,
                    v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_,
                );
                if crate::leanh::lean_obj_tag(v___x_1910_) == 0 {
                    v_a_1911_ = crate::leanh::lean_ctor_get(v___x_1910_, 0);
                    v_isSharedCheck_1926_ = (!crate::leanh::lean_is_exclusive(v___x_1910_)) as u8;
                    if v_isSharedCheck_1926_ == 0 {
                        v___x_1913_ = v___x_1910_;
                        v_isShared_1914_ = v_isSharedCheck_1926_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1911_);
                        crate::leanh::lean_dec(v___x_1910_);
                        v___x_1913_ = crate::leanh::lean_box(0);
                        v_isShared_1914_ = v_isSharedCheck_1926_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1927_ = crate::leanh::lean_ctor_get(v___x_1910_, 0);
                    v_isSharedCheck_1934_ = (!crate::leanh::lean_is_exclusive(v___x_1910_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1929_ = v___x_1910_;
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1927_);
                        crate::leanh::lean_dec(v___x_1910_);
                        v___x_1929_ = crate::leanh::lean_box(0);
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_lawfulOrderLTInst_x3f_1915_ = crate::leanh::lean_ctor_get(v_a_1911_, 8);
                crate::leanh::lean_inc(v_lawfulOrderLTInst_x3f_1915_);
                crate::leanh::lean_dec(v_a_1911_);
                if crate::leanh::lean_obj_tag(v_lawfulOrderLTInst_x3f_1915_) == 0 {
                    v___x_1916_ = 0;
                    v___x_1917_ = crate::leanh::lean_box((v___x_1916_) as usize);
                    if v_isShared_1914_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1913_, 0, v___x_1917_);
                        v___x_1919_ = v___x_1913_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1920_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
                        v___x_1919_ = v_reuseFailAlloc_1920_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1915_, 1);
                    v___x_1921_ = 1;
                    v___x_1922_ = crate::leanh::lean_box((v___x_1921_) as usize);
                    if v_isShared_1914_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1913_, 0, v___x_1922_);
                        v___x_1924_ = v___x_1913_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
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
                    v_reuseFailAlloc_1933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
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
    mut v_a_1935_: *mut crate::leanh::LeanObject,
    mut v_a_1936_: *mut crate::leanh::LeanObject,
    mut v_a_1937_: *mut crate::leanh::LeanObject,
    mut v_a_1938_: *mut crate::leanh::LeanObject,
    mut v_a_1939_: *mut crate::leanh::LeanObject,
    mut v_a_1940_: *mut crate::leanh::LeanObject,
    mut v_a_1941_: *mut crate::leanh::LeanObject,
    mut v_a_1942_: *mut crate::leanh::LeanObject,
    mut v_a_1943_: *mut crate::leanh::LeanObject,
    mut v_a_1944_: *mut crate::leanh::LeanObject,
    mut v_a_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_Lean_Meta_Grind_Order_hasLt(
        v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_,
        v_a_1943_, v_a_1944_, v_a_1945_,
    );
    crate::leanh::lean_dec(v_a_1945_);
    crate::leanh::lean_dec_ref(v_a_1944_);
    crate::leanh::lean_dec(v_a_1943_);
    crate::leanh::lean_dec_ref(v_a_1942_);
    crate::leanh::lean_dec(v_a_1941_);
    crate::leanh::lean_dec_ref(v_a_1940_);
    crate::leanh::lean_dec(v_a_1939_);
    crate::leanh::lean_dec_ref(v_a_1938_);
    crate::leanh::lean_dec(v_a_1937_);
    crate::leanh::lean_dec(v_a_1936_);
    crate::leanh::lean_dec(v_a_1935_);
    return v_res_1947_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_isInt(
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
    mut v_a_1953_: *mut crate::leanh::LeanObject,
    mut v_a_1954_: *mut crate::leanh::LeanObject,
    mut v_a_1955_: *mut crate::leanh::LeanObject,
    mut v_a_1956_: *mut crate::leanh::LeanObject,
    mut v_a_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v_type_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v_a_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1981_: u8 = 0;
    let mut v_a_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1960_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_,
                    v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_,
                );
                if crate::leanh::lean_obj_tag(v___x_1960_) == 0 {
                    v_a_1961_ = crate::leanh::lean_ctor_get(v___x_1960_, 0);
                    crate::leanh::lean_inc(v_a_1961_);
                    crate::leanh::lean_dec_ref_known(v___x_1960_, 1);
                    v___x_1962_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_1953_);
                    if crate::leanh::lean_obj_tag(v___x_1962_) == 0 {
                        v_a_1963_ = crate::leanh::lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_1973_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_1973_ == 0 {
                            v___x_1965_ = v___x_1962_;
                            v_isShared_1966_ = v_isSharedCheck_1973_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1963_);
                            crate::leanh::lean_dec(v___x_1962_);
                            v___x_1965_ = crate::leanh::lean_box(0);
                            v_isShared_1966_ = v_isSharedCheck_1973_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1961_);
                        v_a_1974_ = crate::leanh::lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_1981_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_1981_ == 0 {
                            v___x_1976_ = v___x_1962_;
                            v_isShared_1977_ = v_isSharedCheck_1981_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1974_);
                            crate::leanh::lean_dec(v___x_1962_);
                            v___x_1976_ = crate::leanh::lean_box(0);
                            v_isShared_1977_ = v_isSharedCheck_1981_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1982_ = crate::leanh::lean_ctor_get(v___x_1960_, 0);
                    v_isSharedCheck_1989_ = (!crate::leanh::lean_is_exclusive(v___x_1960_)) as u8;
                    if v_isSharedCheck_1989_ == 0 {
                        v___x_1984_ = v___x_1960_;
                        v_isShared_1985_ = v_isSharedCheck_1989_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1982_);
                        crate::leanh::lean_dec(v___x_1960_);
                        v___x_1984_ = crate::leanh::lean_box(0);
                        v_isShared_1985_ = v_isSharedCheck_1989_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_type_1967_ = crate::leanh::lean_ctor_get(v_a_1961_, 1);
                crate::leanh::lean_inc_ref(v_type_1967_);
                crate::leanh::lean_dec(v_a_1961_);
                v___x_1968_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_1967_,
                        v_a_1963_,
                    );
                crate::leanh::lean_dec(v_a_1963_);
                crate::leanh::lean_dec_ref(v_type_1967_);
                v___x_1969_ = crate::leanh::lean_box((v___x_1968_) as usize);
                if v_isShared_1966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1965_, 0, v___x_1969_);
                    v___x_1971_ = v___x_1965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
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
                    v_reuseFailAlloc_1980_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
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
                    v_reuseFailAlloc_1988_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
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
    mut v_a_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: *mut crate::leanh::LeanObject,
    mut v_a_1994_: *mut crate::leanh::LeanObject,
    mut v_a_1995_: *mut crate::leanh::LeanObject,
    mut v_a_1996_: *mut crate::leanh::LeanObject,
    mut v_a_1997_: *mut crate::leanh::LeanObject,
    mut v_a_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
    mut v_a_2000_: *mut crate::leanh::LeanObject,
    mut v_a_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_Meta_Grind_Order_isInt(
        v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_,
        v_a_1998_, v_a_1999_, v_a_2000_,
    );
    crate::leanh::lean_dec(v_a_2000_);
    crate::leanh::lean_dec_ref(v_a_1999_);
    crate::leanh::lean_dec(v_a_1998_);
    crate::leanh::lean_dec_ref(v_a_1997_);
    crate::leanh::lean_dec(v_a_1996_);
    crate::leanh::lean_dec_ref(v_a_1995_);
    crate::leanh::lean_dec(v_a_1994_);
    crate::leanh::lean_dec_ref(v_a_1993_);
    crate::leanh::lean_dec(v_a_1992_);
    crate::leanh::lean_dec(v_a_1991_);
    crate::leanh::lean_dec(v_a_1990_);
    return v_res_2002_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_OrderM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
}
